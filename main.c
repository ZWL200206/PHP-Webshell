#include "zend_compile.h"
#include "zend_alloc.h"
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <signal.h>
#include <stdint.h>

typedef bool zend_bool;

static HashTable tainted_table;
static HashTable local_tainted_table;
static HashTable local_sink_table;
static HashTable var_source_table;
static HashTable func_source_table;
static HashTable sink_table;
static HashTable sink_var_table;
static HashTable sink_func_table;
static HashTable webshell_table;
// 全局变量值表，用于跟踪已赋值的变量值（用于字符串表达式评估）
static HashTable var_value_table;
// 新增：可疑点表
static HashTable suspect_site_table;
// 新增：动态补充的调用图边（caller -> callee 集合）
static HashTable call_graph_extra;
// 新增：静态调用图（caller -> callee 集合）
static HashTable call_graph_static;
// 当前正在分析的文件名（在入口处赋值）
static zend_string *current_filename = NULL;
// 当前正在分析的函数名（用于记录调用者）
static zend_string *current_function_name = NULL;
// 全局 AST 根节点
static zend_ast *g_root_ast = NULL;
static int tainted_count = 0;
static int local_tainted_count = 0;
static int local_sink_count = 0;
static int sink_count = 0;
static int sink_var_count = 0;
static int sink_func_count = 0;
static int webshell_count = 0;
static int webshell = 0;
static int local_webshell = 0;
static int func_source_count = 0;
// 动态断言命中计数（建议2）
static int dynamic_webshell_hit = 0;

/* 标记：需要动态解析的节点（静态分析无法确定） */
#define AST_NEED_DYNAMIC_RESOLVE 0x1000

static void local_taint_track(zend_ast *ast);
static inline zend_bool ast_kind_is_decl(zend_ast_kind kind);
static inline zend_bool ast_is_name(zend_ast *ast, zend_ast *parent, uint32_t i);
static inline zend_bool ast_is_type(zend_ast *ast, zend_ast *parent, uint32_t i);
static inline zend_bool ast_is_var_name(zend_ast *ast, zend_ast *parent, uint32_t i);
static inline zend_ast **ast_get_children(zend_ast *ast, uint32_t *count);
static void show_tokenname(zend_ast_kind kind);
static void traverse_ast(zend_ast *ast);
static void check_function(zend_ast* ast);
static void taint_propagate(zend_ast* ast, bool local);
static void taint_track(zend_ast *ast);
static void sink_propagate(zend_ast* ast, HashTable* var_table, int* var_count);
static void sink_track(zend_ast *ast, HashTable* var_table, int* var_count);
static void webshell_check(zend_ast *ast, bool local);
static int local_sink_check(zend_ast *ast);
static int has_sink_child(zend_ast *ast);
static void track_assignment(zend_ast *assign_ast, HashTable *var_table);
static void insert_assert_before(zend_ast **stmt_ptr, zend_arena **arena);
static void dynamic_function_analysis(zend_ast *ast);
static zend_string* evaluate_string_expression(zend_ast *expr);
static zend_string* evaluate_strtr_call(zend_ast *call_ast);
static zend_string* evaluate_concat_expression(zend_ast *expr);
static zend_string* evaluate_xor_expression(zend_ast *expr);
static zend_string* evaluate_or_expression(zend_ast *expr);
static zend_string* evaluate_and_expression(zend_ast *expr);
static zend_string* evaluate_string_call(zend_ast *call_ast);
static zend_string* evaluate_str_replace_call(zend_ast *call_ast);
static zend_string* evaluate_base64_decode_call(zend_ast *call_ast);
static zend_string* evaluate_url_decode_call(zend_ast *call_ast, zend_bool raw);
static zend_string* evaluate_rot13_call(zend_ast *call_ast);
static zend_bool is_known_sink_function(zend_string *func_name);
static void add_sink_var_from_assignment(zend_ast *var_node, zend_string *func_name);
static zend_bool is_hex_string(zend_string *str);
static zend_string* hex_decode_string(zend_string *hex_str);
static zend_bool contains_dangerous_function(zend_string *str);
// 栈结构，用于存储节点指针
typedef struct Stack {
    zend_ast** data;
    int top;
    int capacity;
} Stack;


// 初始化栈
void initStack(Stack *stack, int capacity) {
    //Stack* stack = (Stack*)malloc(sizeof(Stack));
    stack->data = (zend_ast**)malloc(sizeof(zend_ast*) * capacity);
    stack->top = 0;
    stack->capacity = capacity;
}

// 判断栈是否满
int isFull(Stack* stack) {
    return stack->top == stack->capacity;
}

// 入栈操作
void push(Stack* stack, zend_ast* item) {
    if (isFull(stack)) {
        // 栈已满，处理溢出情况
        return;
    }
    stack->data[stack->top++] = item;
}

// 判断栈是否空
int isEmpty(Stack* stack) {
    return stack->top == 0;
}

// 出栈操作
zend_ast* pop(Stack* stack) {
    if (isEmpty(stack)) {
        // 栈为空，处理下溢情况
        return NULL;
    }

    return stack->data[--stack->top];
}

// 识别ast节点是声明类型
static inline zend_bool ast_kind_is_decl(zend_ast_kind kind) {
        return kind == ZEND_AST_FUNC_DECL || kind == ZEND_AST_CLOSURE
                || kind == ZEND_AST_ARROW_FUNC
                || kind == ZEND_AST_METHOD || kind == ZEND_AST_CLASS;
}
// 判断当前节点是否代表一个名称
static inline zend_bool ast_is_name(zend_ast *ast, zend_ast *parent, uint32_t i) {
        if (!ast) {
                return 0;
        }
        if (ast->kind != ZEND_AST_ZVAL || Z_TYPE_P(zend_ast_get_zval(ast)) != IS_STRING) {
                return 0;
        }

        if (parent->kind == ZEND_AST_NAME_LIST) {
                return 1;
        }
        if (parent->kind == ZEND_AST_TYPE_INTERSECTION) {
                return 1;
        }
        if (parent->kind == ZEND_AST_TYPE_UNION) {
                return 1;
        }

        if (i == 0) {
                return parent->kind == ZEND_AST_CATCH || parent->kind == ZEND_AST_CLASS
                        || parent->kind == ZEND_AST_PARAM || parent->kind == ZEND_AST_METHOD_REFERENCE
                        || parent->kind == ZEND_AST_CALL || parent->kind == ZEND_AST_CONST
                        || parent->kind == ZEND_AST_NEW || parent->kind == ZEND_AST_STATIC_CALL
                        || parent->kind == ZEND_AST_CLASS_CONST || parent->kind == ZEND_AST_STATIC_PROP
                        || parent->kind == ZEND_AST_PROP_GROUP || parent->kind == ZEND_AST_CLASS_NAME
                        || parent->kind == ZEND_AST_ATTRIBUTE
                        ;
        }

        if (i == 2) {
                return parent->kind == ZEND_AST_CLASS_CONST_GROUP;
        }

        if (i == 1) {
                return parent->kind == ZEND_AST_INSTANCEOF;
        }
        if (i == 3) {
                return parent->kind == ZEND_AST_FUNC_DECL || parent->kind == ZEND_AST_CLOSURE
                        || parent->kind == ZEND_AST_ARROW_FUNC
                        || parent->kind == ZEND_AST_METHOD;
        }

        if (i == 4) {
                return parent->kind == ZEND_AST_CLASS;
        }

        return 0;
}

/* Assumes that ast_is_name is already true */
// 在已确定AST节点是名称的前提下，进一步判断该名称是否表示一个类型
static inline zend_bool ast_is_type(zend_ast *ast, zend_ast *parent, uint32_t i) {
        if (parent->kind == ZEND_AST_TYPE_INTERSECTION) {
                return 1;
        }
        if (parent->kind == ZEND_AST_TYPE_UNION) {
                return 1;
        }
        if (i == 0) {
                return parent->kind == ZEND_AST_PARAM
                        || parent->kind == ZEND_AST_PROP_GROUP
                        ;
        }
        if (i == 2) {
                return parent->kind == ZEND_AST_CLASS_CONST_GROUP;
        }

        if (i == 3) {
                return parent->kind == ZEND_AST_CLOSURE || parent->kind == ZEND_AST_FUNC_DECL
                        || parent->kind == ZEND_AST_ARROW_FUNC
                        || parent->kind == ZEND_AST_METHOD;
        }
        if (i == 4) {
                return parent->kind == ZEND_AST_CLASS;
        }
        return 0;
}
// 判断一个AST节点是否表示一个变量名称
static inline zend_bool ast_is_var_name(zend_ast *ast, zend_ast *parent, uint32_t i) {
        return (parent->kind == ZEND_AST_STATIC && i == 0)
                || (parent->kind == ZEND_AST_CATCH && i == 1 && ast != NULL);
}
// 获取给定AST节点的子节点，并返回子节点数组以及子节点的数量
static inline zend_ast **ast_get_children(zend_ast *ast, uint32_t *count) {
        if (!ast) {
                *count = 0;
                return NULL;
        }
        
        if (ast_kind_is_decl(ast->kind)) {
                zend_ast_decl *decl = (zend_ast_decl *) ast;
                *count = 5;
                return decl->child;
        } else if (zend_ast_is_list(ast)) {
                zend_ast_list *list = zend_ast_get_list(ast);
                if (!list) {
                        *count = 0;
                        return NULL;
                }
                // 限制 children 的最大值，防止越界访问
                uint32_t children_count = list->children;
                // 添加额外的安全检查：确保 children_count 是合理的值
                if (children_count == 0) {
                        *count = 0;
                        return NULL;
                }
                if (children_count > 1000) {
                        children_count = 1000;  // 增加限制以处理大型AST
                }
                *count = children_count;
                // 确保 child 数组指针有效
                if (!list->child) {
                        *count = 0;
                        return NULL;
                }
                return list->child;
        } else {
                *count = zend_ast_get_num_children(ast);
                // 限制 count 的最大值
                if (*count > 100) {
                        *count = 100;  // 增加限制以处理大型AST
                }
                return ast->child;
        }
}

static void show_tokenname(zend_ast_kind kind) {
  switch (kind) {
    case ZEND_AST_ZVAL:
      printf("ZEND_AST_ZVAL\n");
      break;
    case ZEND_AST_CONSTANT:
      printf("ZEND_AST_CONSTANT\n");
      break;
    case ZEND_AST_ZNODE:
      printf("ZEND_AST_ZNODE\n");
      break;
    case ZEND_AST_FUNC_DECL:
      printf("ZEND_AST_FUNC_DECL\n");
      break;
    case ZEND_AST_CLOSURE:
      printf("ZEND_AST_CLOSURE\n");
      break;
    case ZEND_AST_METHOD:
      printf("ZEND_AST_METHOD\n");
      break;
    case ZEND_AST_CLASS:
      printf("ZEND_AST_CLASS\n");
      break;
    case ZEND_AST_ARROW_FUNC:
      printf("ZEND_AST_ARROW_FUNC\n");
      break;
    case ZEND_AST_ARG_LIST:
      printf("ZEND_AST_ARG_LIST\n");
      break;
    case ZEND_AST_ARRAY:
      printf("ZEND_AST_ARRAY\n");
      break;
    case ZEND_AST_ENCAPS_LIST:
      printf("ZEND_AST_ENCAPS_LIST\n");
      break;
    case ZEND_AST_EXPR_LIST:
      printf("ZEND_AST_EXPR_LIST\n");
      break;
    case ZEND_AST_STMT_LIST:
      printf("ZEND_AST_STMT_LIST\n");
      break;
    case ZEND_AST_IF:
      printf("ZEND_AST_IF\n");
      break;
    case ZEND_AST_SWITCH_LIST:
      printf("ZEND_AST_SWITCH_LIST\n");
      break;
    case ZEND_AST_CATCH_LIST:
      printf("ZEND_AST_CATCH_LIST\n");
      break;
    case ZEND_AST_PARAM_LIST:
      printf("ZEND_AST_PARAM_LIST\n");
      break;
    case ZEND_AST_CLOSURE_USES:
      printf("ZEND_AST_CLOSURE_USES\n");
      break;
    case ZEND_AST_PROP_DECL:
      printf("ZEND_AST_PROP_DECL\n");
      break;
    case ZEND_AST_CONST_DECL:
      printf("ZEND_AST_CONST_DECL\n");
      break;
    case ZEND_AST_CLASS_CONST_DECL:
      printf("ZEND_AST_CLASS_CONST_DECL\n");
      break;
    case ZEND_AST_NAME_LIST:
      printf("ZEND_AST_NAME_LIST\n");
      break;
    case ZEND_AST_TRAIT_ADAPTATIONS:
      printf("ZEND_AST_TRAIT_ADAPTATIONS\n");
      break;
    case ZEND_AST_USE:
      printf("ZEND_AST_USE\n");
      break;
    case ZEND_AST_TYPE_UNION:
      printf("ZEND_AST_TYPE_UNION\n");
      break;
    case ZEND_AST_TYPE_INTERSECTION:
      printf("ZEND_AST_TYPE_INTERSECTION\n");
      break;
    case ZEND_AST_ATTRIBUTE_LIST:
      printf("ZEND_AST_ATTRIBUTE_LIST\n");
      break;
    case ZEND_AST_ATTRIBUTE_GROUP:
      printf("ZEND_AST_ATTRIBUTE_GROUP\n");
      break;
    case ZEND_AST_MATCH_ARM_LIST:
      printf("ZEND_AST_MATCH_ARM_LIST\n");
      break;
    case ZEND_AST_MODIFIER_LIST:
      printf("ZEND_AST_MODIFIER_LIST\n");
      break;
    case ZEND_AST_MAGIC_CONST:
      printf("ZEND_AST_MAGIC_CONST\n");
      break;
    case ZEND_AST_TYPE:
      printf("ZEND_AST_TYPE\n");
      break;
    case ZEND_AST_CONSTANT_CLASS:
      printf("ZEND_AST_CONSTANT_CLASS\n");
      break;
    case ZEND_AST_CALLABLE_CONVERT:
      printf("ZEND_AST_CALLABLE_CONVERT\n");
      break;
    case ZEND_AST_VAR:
      printf("ZEND_AST_VAR\n");
      break;
    case ZEND_AST_CONST:
      printf("ZEND_AST_CONST\n");
      break;
    case ZEND_AST_UNPACK:
      printf("ZEND_AST_UNPACK\n");
      break;
    case ZEND_AST_UNARY_PLUS:
      printf("ZEND_AST_UNARY_PLUS\n");
      break;
    case ZEND_AST_UNARY_MINUS:
      printf("ZEND_AST_UNARY_MINUS\n");
      break;
    case ZEND_AST_CAST:
      printf("ZEND_AST_CAST\n");
      break;
    case ZEND_AST_EMPTY:
      printf("ZEND_AST_EMPTY\n");
      break;
    case ZEND_AST_ISSET:
      printf("ZEND_AST_ISSET\n");
      break;
    case ZEND_AST_SILENCE:
      printf("ZEND_AST_SILENCE\n");
      break;
    case ZEND_AST_SHELL_EXEC:
      printf("ZEND_AST_SHELL_EXEC\n");
      break;
    case ZEND_AST_CLONE:
      printf("ZEND_AST_CLONE\n");
      break;
    case ZEND_AST_EXIT:
      printf("ZEND_AST_EXIT\n");
      break;
    case ZEND_AST_PRINT:
      printf("ZEND_AST_PRINT\n");
      break;
    case ZEND_AST_INCLUDE_OR_EVAL:
      printf("ZEND_AST_INCLUDE_OR_EVAL\n");
      break;
    case ZEND_AST_UNARY_OP:
      printf("ZEND_AST_UNARY_OP\n");
      break;
    case ZEND_AST_PRE_INC:
      printf("ZEND_AST_PRE_INC\n");
      break;
    case ZEND_AST_PRE_DEC:
      printf("ZEND_AST_PRE_DEC\n");
      break;
    case ZEND_AST_POST_INC:
      printf("ZEND_AST_POST_INC\n");
      break;
    case ZEND_AST_POST_DEC:
      printf("ZEND_AST_POST_DEC\n");
      break;
    case ZEND_AST_YIELD_FROM:
      printf("ZEND_AST_YIELD_FROM\n");
      break;
    case ZEND_AST_CLASS_NAME:
      printf("ZEND_AST_CLASS_NAME\n");
      break;
    case ZEND_AST_GLOBAL:
      printf("ZEND_AST_GLOBAL\n");
      break;
    case ZEND_AST_UNSET:
      printf("ZEND_AST_UNSET\n");
      break;
    case ZEND_AST_RETURN:
      printf("ZEND_AST_RETURN\n");
      break;
    case ZEND_AST_LABEL:
      printf("ZEND_AST_LABEL\n");
      break;
    case ZEND_AST_REF:
      printf("ZEND_AST_REF\n");
      break;
    case ZEND_AST_HALT_COMPILER:
      printf("ZEND_AST_HALT_COMPILER\n");
      break;
    case ZEND_AST_ECHO:
      printf("ZEND_AST_ECHO\n");
      break;
    case ZEND_AST_THROW:
      printf("ZEND_AST_THROW\n");
      break;
    case ZEND_AST_GOTO:
      printf("ZEND_AST_GOTO\n");
      break;
    case ZEND_AST_BREAK:
      printf("ZEND_AST_BREAK\n");
      break;
    case ZEND_AST_CONTINUE:
      printf("ZEND_AST_CONTINUE\n");
      break;
    case ZEND_AST_DIM:
      printf("ZEND_AST_DIM\n");
      break;
    case ZEND_AST_PROP:
      printf("ZEND_AST_PROP\n");
      break;
    case ZEND_AST_NULLSAFE_PROP:
      printf("ZEND_AST_NULLSAFE_PROP\n");
      break;
    case ZEND_AST_STATIC_PROP:
      printf("ZEND_AST_STATIC_PROP\n");
      break;
    case ZEND_AST_CALL:
      printf("ZEND_AST_CALL\n");
      break;
    case ZEND_AST_CLASS_CONST:
      printf("ZEND_AST_CLASS_CONST\n");
      break;
    case ZEND_AST_ASSIGN:
      printf("ZEND_AST_ASSIGN\n");
      break;
    case ZEND_AST_ASSIGN_REF:
      printf("ZEND_AST_ASSIGN_REF\n");
      break;
    case ZEND_AST_ASSIGN_OP:
      printf("ZEND_AST_ASSIGN_OP\n");
      break;
    case ZEND_AST_BINARY_OP:
      printf("ZEND_AST_BINARY_OP\n");
      break;
    case ZEND_AST_GREATER:
      printf("ZEND_AST_GREATER\n");
      break;
    case ZEND_AST_GREATER_EQUAL:
      printf("ZEND_AST_GREATER_EQUAL\n");
      break;
    case ZEND_AST_AND:
      printf("ZEND_AST_AND\n");
      break;
    case ZEND_AST_OR:
      printf("ZEND_AST_OR\n");
      break;
    case ZEND_AST_ARRAY_ELEM:
      printf("ZEND_AST_ARRAY_ELEM\n");
      break;
    case ZEND_AST_NEW:
      printf("ZEND_AST_NEW\n");
      break;
    case ZEND_AST_INSTANCEOF:
      printf("ZEND_AST_INSTANCEOF\n");
      break;
    case ZEND_AST_YIELD:
      printf("ZEND_AST_YIELD\n");
      break;
    case ZEND_AST_COALESCE:
      printf("ZEND_AST_COALESCE\n");
      break;
    case ZEND_AST_ASSIGN_COALESCE:
      printf("ZEND_AST_ASSIGN_COALESCE\n");
      break;
    case ZEND_AST_STATIC:
      printf("ZEND_AST_STATIC\n");
      break;
    case ZEND_AST_WHILE:
      printf("ZEND_AST_WHILE\n");
      break;
    case ZEND_AST_DO_WHILE:
      printf("ZEND_AST_DO_WHILE\n");
      break;
    case ZEND_AST_IF_ELEM:
      printf("ZEND_AST_IF_ELEM\n");
      break;
    case ZEND_AST_SWITCH:
      printf("ZEND_AST_SWITCH\n");
      break;
    case ZEND_AST_SWITCH_CASE:
      printf("ZEND_AST_SWITCH_CASE\n");
      break;
    case ZEND_AST_DECLARE:
      printf("ZEND_AST_DECLARE\n");
      break;
    case ZEND_AST_USE_TRAIT:
      printf("ZEND_AST_USE_TRAIT\n");
      break;
    case ZEND_AST_TRAIT_PRECEDENCE:
      printf("ZEND_AST_TRAIT_PRECEDENCE\n");
      break;
    case ZEND_AST_METHOD_REFERENCE:
      printf("ZEND_AST_METHOD_REFERENCE\n");
      break;
    case ZEND_AST_NAMESPACE:
      printf("ZEND_AST_NAMESPACE\n");
      break;
    case ZEND_AST_USE_ELEM:
      printf("ZEND_AST_USE_ELEM\n");
      break;
    case ZEND_AST_TRAIT_ALIAS:
      printf("ZEND_AST_TRAIT_ALIAS\n");
      break;
    case ZEND_AST_GROUP_USE:
      printf("ZEND_AST_GROUP_USE\n");
      break;
    case ZEND_AST_ATTRIBUTE:
      printf("ZEND_AST_ATTRIBUTE\n");
      break;
    case ZEND_AST_MATCH:
      printf("ZEND_AST_MATCH\n");
      break;
    case ZEND_AST_MATCH_ARM:
      printf("ZEND_AST_MATCH_ARM\n");
      break;
    case ZEND_AST_NAMED_ARG:
      printf("ZEND_AST_NAMED_ARG\n");
      break;
    case ZEND_AST_METHOD_CALL:
      printf("ZEND_AST_METHOD_CALL\n");
      break;
    case ZEND_AST_NULLSAFE_METHOD_CALL:
      printf("ZEND_AST_NULLSAFE_METHOD_CALL\n");
      break;
    case ZEND_AST_STATIC_CALL:
      printf("ZEND_AST_STATIC_CALL\n");
      break;
    case ZEND_AST_CONDITIONAL:
      printf("ZEND_AST_CONDITIONAL\n");
      break;
    case ZEND_AST_TRY:
      printf("ZEND_AST_TRY\n");
      break;
    case ZEND_AST_CATCH:
      printf("ZEND_AST_CATCH\n");
      break;
    case ZEND_AST_PROP_GROUP:
      printf("ZEND_AST_PROP_GROUP\n");
      break;
    case ZEND_AST_PROP_ELEM:
      printf("ZEND_AST_PROP_ELEM\n");
      break;
    case ZEND_AST_CONST_ELEM:
      printf("ZEND_AST_CONST_ELEM\n");
      break;
    case ZEND_AST_CLASS_CONST_GROUP:
      printf("ZEND_AST_CLASS_CONST_GROUP\n");
      break;
    case ZEND_AST_CONST_ENUM_INIT:
      printf("ZEND_AST_CONST_ENUM_INIT\n");
      break;
    case ZEND_AST_FOR:
      printf("ZEND_AST_FOR\n");
      break;
    case ZEND_AST_FOREACH:
      printf("ZEND_AST_FOREACH\n");
      break;
    case ZEND_AST_ENUM_CASE:
      printf("ZEND_AST_ENUM_CASE\n");
      break;
    case ZEND_AST_PARAM:
      printf("ZEND_AST_PARAM\n");
      break;

    default: break;
  }
}

// Initialize tainted and father properties of the ast.
// Track all nodes in the ast and set tainted = 0.
// Set the father of a node as the node direct point to it.

/* 从 eval 节点向上找，找到它所在的语句（stmt）以及语句列表（stmt_list） */
static zend_ast* find_stmt_and_list_for_node(zend_ast *node, zend_ast **out_stmt_list) {
    zend_ast *cur = node;
    zend_ast *parent = node ? node->father : NULL;

    while (parent) {
        if (parent->kind == ZEND_AST_STMT_LIST) {
            // cur 此时就是那条语句（可能是 eval 本身，也可能是 RETURN/ASSIGN 等）
            if (out_stmt_list) {
                *out_stmt_list = parent;
            }
            return cur;
        }
        cur = parent;
        parent = parent->father;
    }
    if (out_stmt_list) {
        *out_stmt_list = NULL;
    }
    return NULL;
}

static void traverse_ast(zend_ast *ast) {

  uint32_t count;
  Stack* stack = (Stack*)malloc(sizeof(Stack));
  initStack(stack, 10000);  // 增加栈大小以处理大型AST
  push(stack, ast);          // 将根节点加入栈

  while (!isEmpty(stack)) {

      zend_ast* current = pop(stack); // 从栈中取出一个节点
      if (!current) continue;
      if(current->kind > 1000){
         continue;
      }
      current->tainted = 0;
      show_tokenname(current->kind);

      /*
      if (current->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(current);
        if (Z_TYPE_P(zv) == IS_STRING) {
          printf("zval is %s\n", Z_STRVAL_P(zv));
        }
      }
      */

      zend_ast **ast_child = ast_get_children(current,&count);
      if (!ast_child) {
          continue;  // 如果无法获取子节点，跳过
      }
      
      // 限制 count 的最大值，防止越界访问
      if (count > 1000) {
          count = 1000;  // 增加限制以处理大型AST
      }

      // 关键修复：对于非 list 节点，需要特别小心处理
      // 对于使用 struct hack 的节点，ast_child 指向的是节点内部的 child 数组
      // 我们需要确保不会访问超出实际分配范围的内存
      uint32_t actual_count = count;
      if (!zend_ast_is_list(current)) {
          // 对于非 list 节点，使用 zend_ast_get_num_children 获取实际的子节点数量
          uint32_t num_children = zend_ast_get_num_children(current);
          if (num_children < actual_count) {
              actual_count = num_children;  // 使用较小的值
          }
      }

      for (int i = 0; i < actual_count; i++) {
          int reverse_i = actual_count - i - 1;
          if (reverse_i < 0 || reverse_i >= actual_count) {
              continue;  // 防止数组越界
          }
          
          // 对于所有节点类型，都使用 ast_child 指针，但添加边界检查
          zend_ast *child = NULL;
          if (reverse_i < actual_count && ast_child != NULL) {
              child = ast_child[reverse_i];
          }
          
          if (child != NULL) {
              // 验证指针有效性：检查节点是否在有效内存范围内
              // 添加额外的安全检查：确保 child 指针对齐且指向有效内存
              // 检查指针是否对齐到至少 4 字节边界（大多数系统要求）
              if (((uintptr_t)child & 0x3) != 0) {
                  continue;  // 指针未对齐，可能是无效指针
              }
              
              // 尝试安全地读取 kind 字段
              zend_ast_kind kind = child->kind;
              if(kind == 0 || kind > 1000){
                   continue;  // 跳过无效的节点类型
              }
              // 只有在 kind 有效时才设置 father 和入栈
              child->father = current;
              push(stack, child); // 将非空子节点加入栈
          }
      }
  }
  free(stack->data); // 释放栈内存
  free(stack);

}

static void check_function(zend_ast* ast) {
  uint32_t count;
  uint32_t count1;

  if (ast->kind == ZEND_AST_FUNC_DECL) {
    zend_ast** ast_child = ast_get_children(ast,&count);
    zend_string* func_name = ((zend_ast_decl *)ast)->name;
    printf("func name is %s\n", func_name->val);
    zend_ast* param_node = NULL;
    zend_ast* stmt_node = NULL;

    
    for (int i = 0;i < count;i++) {
      if (ast_child[i] != NULL) {
        if (ast_child[i]->kind == ZEND_AST_PARAM_LIST) param_node = ast_child[i];
        if (ast_child[i]->kind == ZEND_AST_STMT_LIST) stmt_node = ast_child[i];
      }
    }

    if (param_node != NULL) {
      show_tokenname(param_node->kind);
      zend_ast **param_list = ast_get_children(param_node,&count1);
    }
    printf("hash clean start\n");
    zend_hash_clean(&local_tainted_table);
    local_tainted_count = 0;

    printf("local_taint_track start\n");
    if (stmt_node != NULL) {
      show_tokenname(stmt_node->kind);
      local_taint_track(stmt_node);
      local_webshell = 0;
      webshell_check(stmt_node, 1);
      printf("local_webshell = %d\n", local_webshell);
      if (local_webshell == 0) {

        zend_ast **param_list = NULL;
        count = 0;

        if (param_node != NULL) {
          show_tokenname(param_node->kind);
          param_list = ast_get_children(param_node,&count);
        }
        printf("hash clean start\n");
        zend_hash_clean(&local_tainted_table);
        local_tainted_count = 0;

        traverse_ast(ast);
        local_webshell = 0;

        printf("param count is %d\n", count);

        for (int i = 0;i < count;i++) {
          zend_ast* name_node = param_list[i]->child[1];
          show_tokenname(name_node->kind);

          zval *zv = zend_ast_get_zval(name_node);
          if (Z_TYPE_P(zv) == IS_STRING) {
            zend_string *var_name = zend_ast_get_str(name_node);
            printf("the tainted param name is %s\n", var_name->val);
            if (!zend_hash_exists(&local_tainted_table, var_name)) {
              zval local_taint_val;
              ZVAL_LONG(&local_taint_val, local_tainted_count);
              local_tainted_count++;
              zend_hash_add(&local_tainted_table, var_name, &local_taint_val);
            }
          }
        }

        local_taint_track(stmt_node);
        webshell_check(stmt_node, 1);
        printf("local_webshell = %d\n", local_webshell);
        if (local_webshell > 0) {
          zval sink_val;
          ZVAL_LONG(&sink_val, sink_count);
          sink_count++;
          printf("add func to sink table\n");
          zend_hash_add(&sink_table, func_name, &sink_val);
        } else {
          zend_hash_clean(&local_sink_table);
          local_sink_count = 0;
          printf("local sink track start\n");
          sink_track(stmt_node, &local_sink_table, &local_sink_count);
          printf("check local sink start\n");
          if (local_sink_check(stmt_node)) {
            zval sink_func_val;
            ZVAL_LONG(&sink_func_val, sink_func_count);
            sink_func_count++;
            printf("add func to sink func table\n");
            zend_hash_add(&sink_func_table, func_name, &sink_func_val);
          }
        }


      } else {
        if (local_webshell == 1) {
          zval webshell_val;
          ZVAL_LONG(&webshell_val, webshell_count);
          webshell_count++;
          printf("add func to webshell table\n");
          zend_hash_add(&webshell_table, func_name, &webshell_val);
        }

        if (local_webshell == 2) {
          zval func_source_val;
          ZVAL_LONG(&func_source_val, func_source_count);
          func_source_count++;
          printf("add func to func source table\n");
          zend_hash_add(&func_source_table, func_name, &func_source_val);
        }

      }
    }
  } 
}

static void taint_propagate(zend_ast* ast, bool local) {
  zend_ast *father_node = ast->father;
  while (father_node != NULL) {
    father_node->tainted = 1;
    show_tokenname(father_node->kind);

    // 如果父节点是 ARG_LIST，继续向上传播
    if (father_node->kind == ZEND_AST_ARG_LIST) {
      // ARG_LIST 的父节点应该是 CALL，继续传播
    }

    if (father_node->kind == ZEND_AST_CALL) { 
      zend_ast *next_node = father_node->child[0];
      if (next_node) {
        next_node->tainted = 1;
      }
      // 标记 CALL 节点本身为污点（如果参数是污点）
      // 这样 webshell_check 就能检测到
    }

    // If the tainted node in the right side of an assign statement,
    // add the variable in the left side to tainted table.
    if (father_node->kind == ZEND_AST_ASSIGN) {
      zend_ast *var_node = father_node->child[0];
      if (var_node && var_node->kind == ZEND_AST_DIM) {
        var_node = var_node->child[0];
        if (!var_node) continue;  // 防止空指针
      }
      if (var_node && var_node->kind == ZEND_AST_VAR) {
         zend_ast *name_node = var_node->child[0];
         if (name_node && name_node->kind == ZEND_AST_ZVAL) {
           zval *zv = zend_ast_get_zval(name_node);
           if (Z_TYPE_P(zv) == IS_STRING) {
            zend_string *var_name = zend_ast_get_str(name_node);
            printf("the tainted var name is %s\n", var_name->val);
            if (local) {
              if (!zend_hash_exists(&local_tainted_table, var_name)) {
                zval local_taint_val;
                ZVAL_LONG(&local_taint_val, local_tainted_count);
                local_tainted_count++;
                zend_hash_add(&local_tainted_table, var_name, &local_taint_val);
              }

            } else {
              if (!zend_hash_exists(&tainted_table, var_name)) {
                zval taint_val;
                ZVAL_LONG(&taint_val, tainted_count);
                tainted_count++;
                zend_hash_add(&tainted_table, var_name, &taint_val);
              }
            }
          }
          
        }
      }
    }

    if (father_node->kind == ZEND_AST_METHOD_CALL) {
      zend_ast *var_node = father_node->child[0];
      if (var_node && var_node->kind == ZEND_AST_VAR) {
         zend_ast *name_node = var_node->child[0];
         if (name_node && name_node->kind == ZEND_AST_ZVAL) {
            zval *zv = zend_ast_get_zval(name_node);
            if (Z_TYPE_P(zv) == IS_STRING) {
             zend_string *var_name = zend_ast_get_str(name_node);
             printf("the tainted class var name is %s\n", var_name->val);
             if (local) {
               if (!zend_hash_exists(&local_tainted_table, var_name)) {
                 zval local_taint_val;
                 ZVAL_LONG(&local_taint_val, local_tainted_count);
                 local_tainted_count++;
                 zend_hash_add(&local_tainted_table, var_name, &local_taint_val);
               }
 
             } else {
               if (!zend_hash_exists(&tainted_table, var_name)) {
                 zval taint_val;
                 ZVAL_LONG(&taint_val, tainted_count);
                 tainted_count++;
                 zend_hash_add(&tainted_table, var_name, &taint_val);
               }
             }
           }
         }
       }
    }


    if (father_node->kind == ZEND_AST_FOREACH) {
      uint32_t count;
      zend_ast **ast_child = ast_get_children(father_node,&count);
      for (int i = 0;i < count;i++) {
        zend_ast *var_node = father_node->child[i];
        if (var_node != NULL) {
          if (var_node->kind == ZEND_AST_VAR) {
            zend_ast *name_node = var_node->child[0];
            if (name_node && name_node->kind == ZEND_AST_ZVAL) {
              zval *zv = zend_ast_get_zval(name_node);
              if (Z_TYPE_P(zv) == IS_STRING) {
                zend_string *var_name = zend_ast_get_str(name_node);
                printf("the tainted var name is %s\n", var_name->val);
                if (local) {
                  if (!(zend_hash_exists(&var_source_table, var_name) || zend_hash_exists(&local_tainted_table, var_name))) {            
                    zval local_taint_val;
                    ZVAL_LONG(&local_taint_val, local_tainted_count);
                    local_tainted_count++;
                    zend_hash_add(&local_tainted_table, var_name, &local_taint_val);
                  }

                } else {
                  if (!(zend_hash_exists(&var_source_table, var_name) || zend_hash_exists(&tainted_table, var_name))) {
                    zval taint_val;
                    ZVAL_LONG(&taint_val, tainted_count);
                    tainted_count++;
                    zend_hash_add(&tainted_table, var_name, &taint_val);
                  }
                }
              }
            }
          }
        }
      }
    }

    father_node = father_node->father;
  }

}

// Firstly set the variables defined in source table (such as _POST, _GET) or in tainted table to tainted.
// Then, track the nodes on the path bewteen root and the tainted node and set them to tainted.
// Finally, if the statement is an assign statement, add the defined variable to the tainted table.
static void taint_track(zend_ast *ast) {

  uint32_t count;
  Stack* stack = (Stack*)malloc(sizeof(Stack));
  initStack(stack, 10000);  // 增加栈大小以处理大型AST
  push(stack, ast);          // 将根节点加入栈

  while (!isEmpty(stack)) {

    zend_ast* current = pop(stack); // 从栈中取出一个节点
    //printf("%d ", current->kind);  // 访问当前节点

    if (current->kind == ZEND_AST_VAR) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        if (zv && Z_TYPE_P(zv) == IS_STRING) {
          zend_string *var_name = zend_ast_get_str(next_node);
          // Check whether the variable is in source table or in tainted table or not.
          if ((zend_hash_exists(&var_source_table, var_name)) || (zend_hash_exists(&tainted_table, var_name))){
            printf("the var name is %s\n", Z_STRVAL_P(zv));
            next_node->tainted = 1; // set node to tainted


            // Set all nodes on the path between root to the tainted node to tainted.
            taint_propagate(next_node, 0);
          }
        }
      }
    }

    // 处理数组访问，如 $_GET['cmd']、$_POST['key'] 等
    if (current->kind == ZEND_AST_DIM) {
      zend_ast *var_node = current->child[0];
      if (var_node && var_node->kind == ZEND_AST_VAR) {
        zend_ast *name_node = var_node->child[0];
        if (name_node && name_node->kind == ZEND_AST_ZVAL) {
          zval *zv = zend_ast_get_zval(name_node);
          if (zv && Z_TYPE_P(zv) == IS_STRING) {
            zend_string *var_name = zend_ast_get_str(name_node);
            // 检查数组的基变量（如 $_GET、$_POST）是否在 source table 中
            if (zend_hash_exists(&var_source_table, var_name)) {
              printf("检测到数组访问污点源: %s[...] (var_name=%s)\n", Z_STRVAL_P(zv), Z_STRVAL_P(zv));
              // 标记整个 DIM 节点为污点
              current->tainted = 1;
              // 向上传播污点
              taint_propagate(current, 0);
            } else if (zend_hash_exists(&tainted_table, var_name)) {
              // 如果数组变量本身在 tainted_table 中，也标记为污点
              printf("检测到数组访问污点变量: %s[...] (var_name=%s)\n", Z_STRVAL_P(zv), Z_STRVAL_P(zv));
              current->tainted = 1;
              taint_propagate(current, 0);
            }
          }
        }
      }
    }

    if (current->kind == ZEND_AST_CALL) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        if (Z_TYPE_P(zv) == IS_STRING) {
          zend_string *func_name = zend_ast_get_str(next_node);
          // Check whether the variable is in source table or in tainted table or not.
          if ((zend_hash_exists(&func_source_table, func_name))){
            printf("the func name is %s\n", Z_STRVAL_P(zv));
            next_node->tainted = 1; // set node to tainted


            // Set all nodes on the path between root to the tainted node to tainted.
            taint_propagate(next_node, 0);
          }
          // 改进：对于 base64_decode, gzinflate 等解码函数，如果参数是污点，结果也应该是污点
          // 或者即使参数不是污点，解码函数的结果也应该被视为可疑（保守策略）
          if (func_name && (
              (ZSTR_LEN(func_name) == 13 && memcmp(ZSTR_VAL(func_name), "base64_decode", 13) == 0) ||
              (ZSTR_LEN(func_name) == 10 && memcmp(ZSTR_VAL(func_name), "gzinflate", 10) == 0) ||
              (ZSTR_LEN(func_name) == 8 && memcmp(ZSTR_VAL(func_name), "urldecode", 8) == 0) ||
              (ZSTR_LEN(func_name) == 12 && memcmp(ZSTR_VAL(func_name), "rawurldecode", 12) == 0) ||
              (ZSTR_LEN(func_name) == 8 && memcmp(ZSTR_VAL(func_name), "str_rot13", 8) == 0))) {
            // 检查参数是否是污点
            zend_ast **children = ast_get_children(current, &count);
            bool should_mark_tainted = false;
            if (children && count > 1) {
              zend_ast *arg_list = children[1];
              if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                zend_ast_list *args = zend_ast_get_list(arg_list);
                if (args && args->children > 0 && args->child[0]) {
                  zend_ast *first_arg = args->child[0];
                  if (first_arg->tainted == 1) {
                    // 参数是污点，标记整个 CALL 节点为污点
                    should_mark_tainted = true;
                    printf("检测到解码函数 %s 的参数是污点，标记结果为污点\n", Z_STRVAL_P(zv));
                  } else {
                    // 即使参数不是污点，解码函数的结果也应该被视为可疑（保守策略）
                    // 因为解码后的内容可能是恶意代码
                    should_mark_tainted = true;
                    printf("检测到解码函数 %s，标记结果为可疑（保守策略）\n", Z_STRVAL_P(zv));
                  }
                }
              }
            }
            if (should_mark_tainted) {
              current->tainted = 1;
              taint_propagate(current, 0);
            }
          }
        }
      }
    }
    
    // 改进：处理字符串拼接（CONCAT），如果任一操作数是污点，结果也应该是污点
    if (current->kind == ZEND_AST_BINARY_OP && current->attr == ZEND_CONCAT) {
      zend_ast *left = current->child[0];
      zend_ast *right = current->child[1];
      if ((left && left->tainted == 1) || (right && right->tainted == 1)) {
        current->tainted = 1;
        printf("检测到字符串拼接包含污点，标记结果为污点\n");
        taint_propagate(current, 0);
      }
    }
    
    // 改进：处理字符串插值（ENCAPS_LIST），如 "$check" 或 "{$var}"
    // ZEND_AST_ENCAPS_LIST 表示包含变量插值的字符串
    if (current->kind == ZEND_AST_ENCAPS_LIST) {
      // 检查所有子节点，如果任一子节点是污点，整个字符串就是污点
      zend_ast **children = ast_get_children(current, &count);
      if (children) {
        for (uint32_t i = 0; i < count; i++) {
          if (children[i] && children[i]->tainted == 1) {
            current->tainted = 1;
            printf("检测到字符串插值包含污点，标记结果为污点\n");
            taint_propagate(current, 0);
            break;
          }
          // 如果子节点是变量，检查变量是否在污点表中
          if (children[i] && children[i]->kind == ZEND_AST_VAR) {
            zend_ast *name_node = children[i]->child[0];
            if (name_node && name_node->kind == ZEND_AST_ZVAL) {
              zval *zv = zend_ast_get_zval(name_node);
              if (zv && Z_TYPE_P(zv) == IS_STRING) {
                zend_string *var_name = zend_ast_get_str(name_node);
                if (var_name && (zend_hash_exists(&tainted_table, var_name) || 
                                 zend_hash_exists(&var_source_table, var_name))) {
                  current->tainted = 1;
                  printf("检测到字符串插值包含污点变量 $%s，标记结果为污点\n", Z_STRVAL_P(zv));
                  taint_propagate(current, 0);
                  break;
                }
              }
            }
          }
        }
      }
    }


    zend_ast **ast_child = ast_get_children(current,&count);

    for (int i = 0; i < count; i++) { // 假设最多10个子节点
        int reverse_i = count - i - 1;
        if (ast_child[reverse_i] != NULL) {
            if (current->kind == ZEND_AST_ASSIGN) {
              i = 1;
              //printf("count is %d\n", count);
              zend_ast *var_node = current->child[0];
              //printf("var node kind is %d, %d\n", var_node->kind, ZEND_AST_VAR);
              if (var_node && var_node->kind == ZEND_AST_VAR) {
                zend_ast *next_node = var_node->child[0];
                //printf("next node kind is %d, %d\n", next_node->kind, ZEND_AST_ZVAL);
                if (next_node && next_node->kind == ZEND_AST_ZVAL) {
                  zval *zv = zend_ast_get_zval(next_node);
                  if (zv && Z_TYPE_P(zv) == IS_STRING) {
                    printf("the var name is %s\n", Z_STRVAL_P(zv));
                    zend_string *var_name = zend_ast_get_str(next_node);
                    if (var_name && zend_hash_exists(&tainted_table, var_name)) {
                      printf("the santized var is %s\n", var_name->val);
                      zend_hash_del(&tainted_table, var_name);
                    }
                  }
                }
              }

            }

            show_tokenname(ast_child[reverse_i]->kind);
            if (ast_child[reverse_i]->kind == ZEND_AST_FUNC_DECL) {
              printf("here\n");
              check_function(ast_child[reverse_i]);
              printf("there\n");
            } else {
              push(stack, ast_child[reverse_i]); // 将非空子节点加入栈
            }
        }
    }
  }
  free(stack->data); // 释放栈内存
  free(stack);

}

// Firstly set the variables defined in source table (such as _POST, _GET) or in tainted table to tainted.
// Then, track the nodes on the path bewteen root and the tainted node and set them to tainted.
// Finally, if the statement is an assign statement, add the defined variable to the tainted table.
static void local_taint_track(zend_ast *ast) {

  uint32_t count;
  Stack* stack = (Stack*)malloc(sizeof(Stack));
  initStack(stack, 10000);  // 增加栈大小以处理大型AST
  push(stack, ast);          // 将根节点加入栈

  while (!isEmpty(stack)) {

    zend_ast* current = pop(stack); // 从栈中取出一个节点
    //printf("%d ", current->kind);  // 访问当前节点

    if (current->kind == ZEND_AST_VAR) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        if (zv && Z_TYPE_P(zv) == IS_STRING) {
          zend_string *var_name = zend_ast_get_str(next_node);
          // Check whether the variable is in source table or in tainted table or not.
          if ((zend_hash_exists(&var_source_table, var_name)) || (zend_hash_exists(&local_tainted_table, var_name))){
            printf("the var name is %s\n", Z_STRVAL_P(zv));
            next_node->tainted = 1; // set node to tainted


            // Set all nodes on the path between root to the tainted node to tainted.
            taint_propagate(next_node, 1);
          }
        }
      }
    }

    // 处理数组访问，如 $_GET['cmd']、$_POST['key'] 等（本地污点追踪）
    if (current->kind == ZEND_AST_DIM) {
      zend_ast *var_node = current->child[0];
      if (var_node && var_node->kind == ZEND_AST_VAR) {
        zend_ast *name_node = var_node->child[0];
        if (name_node && name_node->kind == ZEND_AST_ZVAL) {
          zval *zv = zend_ast_get_zval(name_node);
          if (zv && Z_TYPE_P(zv) == IS_STRING) {
            zend_string *var_name = zend_ast_get_str(name_node);
            // 检查数组的基变量（如 $_GET、$_POST）是否在 source table 中
            if (zend_hash_exists(&var_source_table, var_name)) {
              printf("检测到数组访问污点源: %s[...] (var_name=%s, local)\n", Z_STRVAL_P(zv), Z_STRVAL_P(zv));
              // 标记整个 DIM 节点为污点
              current->tainted = 1;
              // 向上传播污点
              taint_propagate(current, 1);
            } else if (zend_hash_exists(&local_tainted_table, var_name) || zend_hash_exists(&tainted_table, var_name)) {
              // 如果数组变量本身在 tainted_table 中，也标记为污点
              printf("检测到数组访问污点变量: %s[...] (var_name=%s, local)\n", Z_STRVAL_P(zv), Z_STRVAL_P(zv));
              current->tainted = 1;
              taint_propagate(current, 1);
            }
          }
        }
      }
    }

    if (current->kind == ZEND_AST_CALL) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        if (Z_TYPE_P(zv) == IS_STRING) {
          zend_string *func_name = zend_ast_get_str(next_node);
          // Check whether the variable is in source table or in tainted table or not.
          if ((zend_hash_exists(&func_source_table, func_name))){
            printf("the func name is %s\n", Z_STRVAL_P(zv));
            next_node->tainted = 1; // set node to tainted


            // Set all nodes on the path between root to the tainted node to tainted.
            taint_propagate(next_node, 1);
          }
        }
      }
    }


    zend_ast **ast_child = ast_get_children(current,&count);

    for (int i = 0; i < count; i++) { // 假设最多10个子节点
        int reverse_i = count - i - 1;
        if (ast_child[reverse_i] != NULL) {
            if (current->kind == ZEND_AST_ASSIGN) {
              i = 1;
              //printf("count is %d\n", count);
              zend_ast *var_node = current->child[0];
              //printf("var node kind is %d, %d\n", var_node->kind, ZEND_AST_VAR);
              if (var_node && var_node->kind == ZEND_AST_VAR) {
                zend_ast *next_node = var_node->child[0];
                //printf("next node kind is %d, %d\n", next_node->kind, ZEND_AST_ZVAL);
                if (next_node && next_node->kind == ZEND_AST_ZVAL) {
                  zval *zv = zend_ast_get_zval(next_node);
                  printf("the var name is %s\n", Z_STRVAL_P(zv));
                  if (zv && Z_TYPE_P(zv) == IS_STRING) {
                    zend_string *var_name = zend_ast_get_str(next_node);
                    if (var_name && zend_hash_exists(&local_tainted_table, var_name)) {
                      printf("the santized var is %s\n", var_name->val);
                      zend_hash_del(&local_tainted_table, var_name);
                    }
                  }
                }
              }

            }

            push(stack, ast_child[reverse_i]); // 将非空子节点加入栈
        }
    }
  }
  free(stack->data); // 释放栈内存
  free(stack);

}

static void sink_propagate(zend_ast* ast, HashTable* var_table, int* var_count) {
  zend_ast *father_node = ast->father;
  while (father_node != NULL) {
    //father_node->tainted = 1;
    // If the tainted node in the right side of an assign statement,
    // add the variable in the left side to tainted table.
    if (father_node->kind == ZEND_AST_ASSIGN) {
      zend_ast *var_node = father_node->child[0];
      if (var_node && var_node->kind == ZEND_AST_DIM) {
        var_node = var_node->child[0];
        if (!var_node) return;  // 防止空指针
      }
      if (var_node && var_node->kind == ZEND_AST_VAR) {
         zend_ast *name_node = var_node->child[0];
         if (name_node) {
           zend_string *var_name = zend_ast_get_str(name_node);
           if (var_name) {
             printf("the sink var name is %s\n", var_name->val);
             if (!zend_hash_exists(var_table, var_name)) {
               zval sink_var_val;
               ZVAL_LONG(&sink_var_val, *var_count);
               (*var_count)++;
               zend_hash_add(var_table, var_name, &sink_var_val);
             }
           }
         }
       }
    }

    father_node = father_node->father;
  }

}

// Firstly set the variables defined in source table (such as _POST, _GET) or in tainted table to tainted.
// Then, track the nodes on the path bewteen root and the tainted node and set them to tainted.
// Finally, if the statement is an assign statement, add the defined variable to the tainted table.
static void sink_track(zend_ast *ast, HashTable* var_table, int* var_count) {

  uint32_t count;
  Stack* stack = (Stack*)malloc(sizeof(Stack));
  initStack(stack, 10000);  // 增加栈大小以处理大型AST
  push(stack, ast);          // 将根节点加入栈

  while (!isEmpty(stack)) {

    zend_ast* current = pop(stack); // 从栈中取出一个节点
    //printf("%d ", current->kind);  // 访问当前节点

    if (current->kind == ZEND_AST_ZVAL) {
      zval *zv = zend_ast_get_zval(current);
      if (Z_TYPE_P(zv) == IS_STRING) {
        zend_string *var_val = zend_ast_get_str(current);
        if (zend_hash_exists(&sink_table, var_val)) {
          printf("the sink var is %s\n", var_val->val);
          sink_propagate(current, var_table, var_count);
        }
      }
    }

    if (current->kind == ZEND_AST_VAR) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        if (zv) {
          printf("the var name is %s\n", Z_STRVAL_P(zv));
          if (Z_TYPE_P(zv) == IS_STRING) {
            zend_string *var_name = zend_ast_get_str(next_node);
            if (var_name && zend_hash_exists(var_table, var_name)) {
              printf("the sink var is %s\n", var_name->val);
              sink_propagate(current, var_table, var_count);
            }
          }
        }
      }
    }

    if (current->kind == ZEND_AST_CALL) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        printf("the var name is %s\n", Z_STRVAL_P(zv));
        if (Z_TYPE_P(zv) == IS_STRING) {
          zend_string *func_name = zend_ast_get_str(next_node);
          if (zend_hash_exists(&sink_func_table, func_name)) {
            printf("the sink func is %s\n", func_name->val);
            sink_propagate(current, var_table, var_count);
          }
        }
      }
    }

    zend_ast **ast_child = ast_get_children(current,&count);

    for (int i = 0; i < count; i++) { // 假设最多10个子节点
        int reverse_i = count - i - 1;
        if (ast_child[reverse_i] != NULL) {
            if (current->kind == ZEND_AST_ASSIGN) {
              i = 1;
              zend_ast *var_node = current->child[0];
              zend_ast *expr_node = current->child[1];
              //printf("var node kind is %d, %d\n", var_node->kind, ZEND_AST_VAR);
              if (var_node && var_node->kind == ZEND_AST_VAR) {
                zend_ast *next_node = var_node->child[0];
                //printf("next node kind is %d, %d\n", next_node->kind, ZEND_AST_ZVAL);
                if (next_node && next_node->kind == ZEND_AST_ZVAL) {
                  zval *zv = zend_ast_get_zval(next_node);
                  if (zv && Z_TYPE_P(zv) == IS_STRING) {
                    printf("the var name is %s\n", Z_STRVAL_P(zv));
                    zend_string *var_name = zend_ast_get_str(next_node);
                    
                    // 检查右侧表达式是否评估为危险函数名
                    if (expr_node) {
                      zend_string *resolved = evaluate_string_expression(expr_node);
                      if (resolved) {
                        printf("评估赋值表达式结果: %s\n", ZSTR_VAL(resolved));
                        
                        // 将变量值存储到 var_value_table 中（用于后续表达式评估）
                        zval var_val_zv;
                        ZVAL_STR(&var_val_zv, zend_string_copy(resolved));
                        zend_hash_update(&var_value_table, var_name, &var_val_zv);
                        
                        if (is_known_sink_function(resolved)) {
                          // 如果变量已经在 sink_var_table 中，保留它
                          // 如果不在，添加它
                          if (!zend_hash_exists(var_table, var_name)) {
                            zval sink_var_val;
                            ZVAL_LONG(&sink_var_val, *var_count);
                            (*var_count)++;
                            zend_hash_add(var_table, var_name, &sink_var_val);
                            printf("检测到危险函数变量赋值: $%s = %s，已添加到 sink_var_table\n", 
                                   var_name->val, ZSTR_VAL(resolved));
                          } else {
                            printf("变量 $%s 被重新赋值为危险函数 %s，保留在 sink_var_table\n", 
                                   var_name->val, ZSTR_VAL(resolved));
                          }
                        } else {
                          // 改进：如果右侧是 pack 函数调用的结果，且该变量后续被用于函数调用，也应该标记为可疑
                          // 因为 pack 经常被用于混淆函数名
                          // 检查表达式是否是 pack 函数调用
                          bool is_pack_result = false;
                          if (expr_node && expr_node->kind == ZEND_AST_CALL) {
                            zend_ast *func_name_node = expr_node->child[0];
                            if (func_name_node && func_name_node->kind == ZEND_AST_ZVAL) {
                              zval *func_zv = zend_ast_get_zval(func_name_node);
                              if (func_zv && Z_TYPE_P(func_zv) == IS_STRING) {
                                const char *func_name_str = Z_STRVAL_P(func_zv);
                                if (strcmp(func_name_str, "pack") == 0) {
                                  is_pack_result = true;
                                  printf("DEBUG: 检测到变量 $%s 被赋值为 pack 函数调用的结果，标记为可疑\n", var_name->val);
                                }
                              }
                            }
                            // 检查是否是变量函数调用 pack（如 $i('c*', ...)）
                            if (func_name_node && func_name_node->kind == ZEND_AST_VAR) {
                              zend_ast *var_name_node = func_name_node->child[0];
                              if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                                zval *var_zv = zend_ast_get_zval(var_name_node);
                                if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                                  // 检查变量值是否是 "pack"
                                  zval *var_val = zend_hash_find(&var_value_table, zend_ast_get_str(var_name_node));
                                  if (var_val && Z_TYPE_P(var_val) == IS_STRING) {
                                    const char *var_val_str = Z_STRVAL_P(var_val);
                                    if (strcmp(var_val_str, "pack") == 0) {
                                      is_pack_result = true;
                                      printf("DEBUG: 检测到变量 $%s 被赋值为变量函数 pack 调用的结果，标记为可疑\n", var_name->val);
                                    }
                                  }
                                }
                              }
                            }
                          }
                          // 如果右侧不是危险函数，且变量在 sink_var_table 中，删除它
                          // 但如果右侧是 pack 函数调用的结果，保留它（因为可能是混淆的函数名）
                          if (zend_hash_exists(var_table, var_name)) {
                            if (!is_pack_result) {
                              printf("变量 $%s 被重新赋值为非危险函数 %s，从 sink_var_table 中删除\n", 
                                     var_name->val, ZSTR_VAL(resolved));
                              zend_hash_del(var_table, var_name);
                            } else {
                              printf("变量 $%s 被赋值为 pack 函数调用的结果，保留在 sink_var_table（可能是混淆的函数名）\n", 
                                     var_name->val);
                            }
                          } else if (is_pack_result) {
                            // 如果变量不在 sink_var_table 中，但右侧是 pack 函数调用的结果，也添加它
                            zval sink_var_val;
                            ZVAL_LONG(&sink_var_val, *var_count);
                            (*var_count)++;
                            zend_hash_add(var_table, var_name, &sink_var_val);
                            printf("检测到 pack 函数调用结果赋值: $%s = pack(...)，已添加到 sink_var_table（可能是混淆的函数名）\n", 
                                   var_name->val);
                          }
                        }
                        zend_string_release(resolved);
                      }
                    }
                  }
                }
              }

            }
            push(stack, ast_child[reverse_i]); // 将非空子节点加入栈
        }
    }
  }
  free(stack->data); // 释放栈内存
  free(stack);

}


// Firstly set the variables defined in source table (such as _POST, _GET) or in tainted table to tainted.
// Then, track the nodes on the path bewteen root and the tainted node and set them to tainted.
// Finally, if the statement is an assign statement, add the defined variable to the tainted table.
static int has_sink_child(zend_ast *ast) {

  uint32_t count;
  Stack* stack = (Stack*)malloc(sizeof(Stack));
  initStack(stack, 10000);  // 增加栈大小以处理大型AST
  push(stack, ast);          // 将根节点加入栈

  printf("has sink child start\n");

  while (!isEmpty(stack)) {

    zend_ast* current = pop(stack); // 从栈中取出一个节点
    //printf("%d ", current->kind);  // 访问当前节点

    if (current->kind == ZEND_AST_ZVAL) {
      zval *zv = zend_ast_get_zval(current);
      if (Z_TYPE_P(zv) == IS_STRING) {
        zend_string *var_val = zend_ast_get_str(current);
        if (zend_hash_exists(&sink_table, var_val)) {
          printf("the sink var is %s\n", var_val->val);
          return 1;
        }
      }
    }

    if (current->kind == ZEND_AST_VAR) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        if (zv && Z_TYPE_P(zv) == IS_STRING) {
          printf("the var name is %s\n", Z_STRVAL_P(zv));
          zend_string *var_name = zend_ast_get_str(next_node);
          if (var_name && zend_hash_exists(&local_sink_table, var_name)) {
            printf("the sink var is %s\n", var_name->val);
            return 1;
          }
        }
      }
    }

    if (current->kind == ZEND_AST_CALL) {
      zend_ast *next_node = current->child[0];
      if (next_node && next_node->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(next_node);
        if (zv && Z_TYPE_P(zv) == IS_STRING) {
          printf("the var name is %s\n", Z_STRVAL_P(zv));
          zend_string *func_name = zend_ast_get_str(next_node);
          if (func_name && zend_hash_exists(&sink_func_table, func_name)) {
            printf("the sink func is %s\n", func_name->val);
            return 1;
          }
        }
      }
    }

    zend_ast **ast_child = ast_get_children(current,&count);

    for (int i = 0; i < count; i++) { // 假设最多10个子节点
        int reverse_i = count - i - 1;
        if (ast_child[reverse_i] != NULL) {
            push(stack, ast_child[reverse_i]); // 将非空子节点加入栈
        }
    }
  }
  free(stack->data); // 释放栈内存
  free(stack);

  return 0;
}

// Check whether the input script is a webshell or not.
// If there is a node which is a sink function or statement and tainted,
// the input script is a webshell.
static int local_sink_check(zend_ast *ast) {
  uint32_t count;
  Stack* stack = (Stack*)malloc(sizeof(Stack));
  initStack(stack, 10000);  // 增加栈大小以处理大型AST
  push(stack, ast);          // 将根节点加入栈
          
  while (!isEmpty(stack)) {
        
      zend_ast* current = pop(stack); // 从栈中取出一个节点

      if (current->kind == ZEND_AST_RETURN) {
        printf("current node is return\n");
        if (has_sink_child(current)) {
          return 1;
        }
      }
   
      zend_ast **ast_child = ast_get_children(current,&count);

      for (int i = 0; i < count; i++) { // 假设最多10个子节点
          int reverse_i = count - i - 1;
          if (ast_child[reverse_i] != NULL) {
              //if (ast_child[reverse_i]->kind != ZEND_AST_RETURN)
                push(stack, ast_child[reverse_i]); // 将非空子节点加入栈
          }
      }
  }
  free(stack->data); // 释放栈内存
  free(stack);

  return 0;
}

// Check whether the input script is a webshell or not.
// If there is a node which is a sink function or statement and tainted,
// the input script is a webshell.
static void webshell_check(zend_ast *ast, bool local) {
  uint32_t count;
  Stack* stack = (Stack*)malloc(sizeof(Stack));
  initStack(stack, 10000);  // 增加栈大小以处理大型AST
  push(stack, ast);          // 将根节点加入栈
  
  int node_count = 0;  // 调试：统计遍历的节点数

  while (!isEmpty(stack)) {
      
      zend_ast* current = pop(stack); // 从栈中取出一个节点
      if (!current) continue;
      node_count++;
      
      // 调试：每处理 100 个节点输出一次
      if (node_count % 100 == 0) {
        printf("DEBUG: webshell_check 已处理 %d 个节点，当前节点 kind=%d\n", node_count, current->kind);
      }

    // Check whether the node is a sink and tainted.
    // eval($_POST['cmd'])
    // include $_POST['file']
    // require $_FILES['test']

    // 检查字符串常量中是否包含webshell特征
    if (current->kind == ZEND_AST_ZVAL) {
      zval *zv = zend_ast_get_zval(current);
      if (zv && Z_TYPE_P(zv) == IS_STRING) {
        const char *str_val = Z_STRVAL_P(zv);
        size_t str_len = Z_STRLEN_P(zv);
        
        // 检查是否包含webshell特征字符串
        const char *webshell_signatures[] = {
          "wso_version", "WSO_VERSION", "wso_",
          "backdoor", "Backdoor", "BACKDOOR",
          "webshell", "WebShell", "WEBSHELL",
          "c99shell", "C99Shell", "C99SHELL",
          "r57shell", "R57Shell", "R57SHELL",
          "phpspy", "PHPSpy", "PHPSPY",
          "zcg:function", "XSLTProcessor", "registerPHPFunctions"
        };
        int signature_count = sizeof(webshell_signatures) / sizeof(webshell_signatures[0]);
        
        for (int i = 0; i < signature_count; i++) {
          if (strstr(str_val, webshell_signatures[i]) != NULL) {
            printf("检测到字符串常量中包含webshell特征: %s (在字符串中发现: %s)\n", 
                   webshell_signatures[i], str_val);
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
            break;
          }
        }
        
        // 检查序列化数据中的webshell特征
        if (strstr(str_val, "\"pass\"") != NULL || 
            strstr(str_val, "\"backdoor\"") != NULL ||
            strstr(str_val, "\"wso_version\"") != NULL ||
            (strstr(str_val, "s:4:\"pass\"") != NULL) ||
            (strstr(str_val, "s:8:\"backdoor\"") != NULL) ||
            (strstr(str_val, "s:11:\"wso_version\"") != NULL)) {
          printf("检测到字符串常量中包含序列化数据中的webshell特征\n");
          if (!local)
            webshell = 1;
          else
            local_webshell = 1;
        }
        
        // 检查XSLT相关的webshell特征
        if (strstr(str_val, "zcg:function") != NULL) {
          // 检查是否包含危险函数调用
          if (strstr(str_val, "assert") != NULL || 
              strstr(str_val, "eval") != NULL ||
              strstr(str_val, "exec") != NULL ||
              strstr(str_val, "system") != NULL) {
            printf("检测到字符串常量中包含XSLT webshell特征: zcg:function 调用危险函数\n");
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          }
        }
        
        // 检查XML/XSL中是否包含危险函数调用模式
        if ((strstr(str_val, "assert(") != NULL && strstr(str_val, "$_POST") != NULL) ||
            (strstr(str_val, "assert(") != NULL && strstr(str_val, "$_GET") != NULL) ||
            (strstr(str_val, "assert(") != NULL && strstr(str_val, "$_REQUEST") != NULL) ||
            (strstr(str_val, "eval(") != NULL && strstr(str_val, "$_POST") != NULL) ||
            (strstr(str_val, "eval(") != NULL && strstr(str_val, "$_GET") != NULL) ||
            (strstr(str_val, "eval(") != NULL && strstr(str_val, "$_REQUEST") != NULL)) {
          printf("检测到字符串常量中包含危险函数调用模式（如 assert(\$_POST[...])）\n");
          if (!local)
            webshell = 1;
          else
            local_webshell = 1;
        }
        
        // 检查字符串中是否包含其他危险函数调用模式（如 system($_GET[...]), exec($_POST[...]) 等）
        if ((strstr(str_val, "system(") != NULL && (strstr(str_val, "$_GET") != NULL || strstr(str_val, "$_POST") != NULL || strstr(str_val, "$_REQUEST") != NULL)) ||
            (strstr(str_val, "exec(") != NULL && (strstr(str_val, "$_GET") != NULL || strstr(str_val, "$_POST") != NULL || strstr(str_val, "$_REQUEST") != NULL)) ||
            (strstr(str_val, "shell_exec(") != NULL && (strstr(str_val, "$_GET") != NULL || strstr(str_val, "$_POST") != NULL || strstr(str_val, "$_REQUEST") != NULL)) ||
            (strstr(str_val, "passthru(") != NULL && (strstr(str_val, "$_GET") != NULL || strstr(str_val, "$_POST") != NULL || strstr(str_val, "$_REQUEST") != NULL))) {
          printf("检测到字符串常量中包含危险函数调用模式（如 system(\$_GET[...])）\n");
          if (!local)
            webshell = 1;
          else
            local_webshell = 1;
        }
        
        // 检查SQL注入特征（INTO OUTFILE）
        if (strstr(str_val, "INTO OUTFILE") != NULL || strstr(str_val, "into outfile") != NULL ||
            strstr(str_val, "INTO outfile") != NULL || strstr(str_val, "into OUTFILE") != NULL) {
          // 如果包含 INTO OUTFILE 且包含危险函数或超全局变量，标记为可疑
          if (strstr(str_val, "system") != NULL || strstr(str_val, "exec") != NULL ||
              strstr(str_val, "eval") != NULL || strstr(str_val, "assert") != NULL ||
              strstr(str_val, "$_GET") != NULL || strstr(str_val, "$_POST") != NULL ||
              strstr(str_val, "$_REQUEST") != NULL) {
            printf("检测到字符串常量中包含SQL注入特征（INTO OUTFILE）且包含危险函数或超全局变量\n");
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          } else {
            // 即使不包含危险函数，INTO OUTFILE 本身也很可疑（SQL注入写入文件）
            printf("检测到字符串常量中包含SQL注入特征（INTO OUTFILE）\n");
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          }
        }
      }
    }

    if ((current->kind == ZEND_AST_RETURN) && (current->tainted == 1) && (local)) {
      local_webshell = 2;
    }

    // 检测 eval() 调用
    // 即使参数无法静态求值，eval() 调用本身也是危险的
    if (current->kind == ZEND_AST_INCLUDE_OR_EVAL) {
      printf("DEBUG: 检测到 ZEND_AST_INCLUDE_OR_EVAL 节点 (attr=%d, tainted=%d)\n", current->attr, current->tainted);
      // 检查是否是 eval（而不是 include/require）
      // ZEND_AST_INCLUDE_OR_EVAL 的 attr 字段可以区分类型
      // ZEND_EVAL = (1<<0) = 1, ZEND_INCLUDE = (1<<1) = 2, ZEND_INCLUDE_ONCE = (1<<2) = 4, 
      // ZEND_REQUIRE = (1<<3) = 8, ZEND_REQUIRE_ONCE = (1<<4) = 16
      // 所有 eval() 调用都应该被检测，无论参数是否可静态求值
      if (current->attr == ZEND_EVAL || current->attr == 1) {
        // eval() 调用，无论参数是否可静态求值，都是危险的
        printf("检测到 eval() 调用 (attr=%d)\n", current->attr);
        if (!local)
          webshell = 1;
        else
          local_webshell = 1;
      } else if (current->tainted == 1) {
        // include/require 且参数被污染
        printf("检测到 include/require 调用且参数被污染 (attr=%d)\n", current->attr);
        if (!local)
          webshell = 1;
        else
          local_webshell = 1;
      } else {
        // 对于混淆代码，即使 attr 不是 ZEND_EVAL，如果参数是变量（可能是混淆的），也应该检测
        // 检查参数是否是变量或复杂表达式（可能是混淆的）
        if (current->child && current->child[0]) {
          zend_ast *arg = current->child[0];
          // 如果参数是变量或包含位运算的表达式，可能是混淆的 eval
          if (arg->kind == ZEND_AST_VAR || 
              arg->kind == ZEND_AST_CALL ||
              (arg->kind == ZEND_AST_BINARY_OP && 
               (arg->attr == ZEND_BW_XOR || arg->attr == ZEND_BW_OR || arg->attr == ZEND_BW_AND))) {
            printf("检测到可疑的 eval/include 调用（参数可能是混淆的，attr=%d, arg_kind=%d）\n", current->attr, arg->kind);
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          } else {
            // 即使参数不是变量，如果是 eval 调用，也应该检测（可能是 attr 值不正确）
            // 为了安全起见，所有 ZEND_AST_INCLUDE_OR_EVAL 节点都应该被检测
            printf("警告: 检测到 ZEND_AST_INCLUDE_OR_EVAL 节点但未匹配任何条件 (attr=%d, arg_kind=%d)，默认标记为可疑\n", 
                   current->attr, arg ? arg->kind : -1);
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          }
        } else {
          // 没有参数，但仍然是 eval/include 调用，应该检测
          printf("警告: 检测到 ZEND_AST_INCLUDE_OR_EVAL 节点但没有参数 (attr=%d)，默认标记为可疑\n", current->attr);
          if (!local)
            webshell = 1;
          else
            local_webshell = 1;
        }
      }
    }

    if ((current->kind == ZEND_AST_SHELL_EXEC) && (current->tainted == 1)){
      if (!local)
        webshell = 1;
      else
        local_webshell = 1;
    }

    if (current->kind == ZEND_AST_METHOD_CALL) {
      if (current->tainted == 1) {
        if (!local)
          webshell = 1;
        else
          local_webshell = 1;
      }
      
      // 检测 __invoke 方法调用（通常用于动态调用函数）
      zend_ast **children = ast_get_children(current, &count);
      if (children && count >= 2) {
        zend_ast *method_node = children[1];
        if (method_node && method_node->kind == ZEND_AST_ZVAL) {
          zval *zv = zend_ast_get_zval(method_node);
          if (zv && Z_TYPE_P(zv) == IS_STRING) {
            zend_string *method_name = zend_ast_get_str(method_node);
            if (method_name && ZSTR_LEN(method_name) == 8 && 
                memcmp(ZSTR_VAL(method_name), "__invoke", 8) == 0) {
              // 检查参数是否包含污点源
              if (current->tainted == 1 || (children[2] && children[2]->tainted == 1)) {
                printf("检测到可疑的 __invoke 方法调用（可能用于动态调用函数），且参数是污点源\n");
                if (!local)
                  webshell = 1;
                else
                  local_webshell = 1;
              } else {
                // 即使参数不是污点，__invoke 调用本身也很可疑（通常用于混淆）
                printf("检测到可疑的 __invoke 方法调用（可能用于动态调用函数）\n");
                if (!local)
                  webshell = 1;
                else
                  local_webshell = 1;
              }
            }
          }
        }
      }

      /*
      if (!webshell) {
        zend_ast *name_node = current->child[0];
        if (name_node->kind == ZEND_AST_VAR)
          name_node = name_node->child[0];
        zval *zv = zend_ast_get_zval(name_node);
        if (Z_TYPE_P(zv) == IS_STRING) {
          zend_string *var_name = zend_ast_get_str(name_node);
          if (zend_hash_exists(&tainted_table, var_name)) {
            zend_ast *method_node = current->child[1];
            zval *zv1 = zend_ast_get_zval(method_node);
            if (Z_TYPE_P(zv1) == IS_STRING) {
              zend_string *method_name = zend_ast_get_str(method_node);
              if (zend_hash_exists(&sink_table, method_name)) {
                webshell = 1;
              }
            }
          }
        }
      }
      */
    }
    
    // 检测静态方法调用 Closure::fromCallable
    if (current->kind == ZEND_AST_STATIC_CALL) {
      zend_ast **children = ast_get_children(current, &count);
      if (children && count >= 2) {
        zend_ast *class_node = children[0];
        zend_ast *method_node = children[1];
        if (class_node && class_node->kind == ZEND_AST_ZVAL &&
            method_node && method_node->kind == ZEND_AST_ZVAL) {
          zval *class_zv = zend_ast_get_zval(class_node);
          zval *method_zv = zend_ast_get_zval(method_node);
          if (class_zv && Z_TYPE_P(class_zv) == IS_STRING &&
              method_zv && Z_TYPE_P(method_zv) == IS_STRING) {
            zend_string *class_name = zend_ast_get_str(class_node);
            zend_string *method_name = zend_ast_get_str(method_node);
            if (class_name && ZSTR_LEN(class_name) == 8 &&
                memcmp(ZSTR_VAL(class_name), "Closure", 8) == 0 &&
                method_name && ZSTR_LEN(method_name) == 12 &&
                memcmp(ZSTR_VAL(method_name), "fromCallable", 12) == 0) {
              // 检查参数是否包含污点源
              if (current->tainted == 1 || (children[2] && children[2]->tainted == 1)) {
                printf("检测到可疑的 Closure::fromCallable 调用（用于动态调用函数），且参数是污点源\n");
                if (!local)
                  webshell = 1;
                else
                  local_webshell = 1;
              } else {
                // 即使参数不是污点，Closure::fromCallable 调用本身也很可疑（通常用于混淆）
                printf("检测到可疑的 Closure::fromCallable 调用（用于动态调用函数）\n");
                if (!local)
                  webshell = 1;
                else
                  local_webshell = 1;
              }
            }
          }
        }
      }
    }

    if (current->kind == ZEND_AST_CALL) {
      zend_ast *name_node = current->child[0];
      if (name_node) {
        // assert($_POST['cmd'])
        if (name_node->kind == ZEND_AST_ZVAL) {
          zval *zv = zend_ast_get_zval(name_node);
          if (zv && Z_TYPE_P(zv) == IS_STRING) {
            zend_string *func_name = zend_ast_get_str(name_node);
            printf("DEBUG: 检测到函数调用: %s (kind=%d, tainted=%d)\n", Z_STRVAL_P(zv), current->kind, current->tainted);
            printf("DEBUG: sink_func_table存在=%d, sink_table存在=%d, webshell_table存在=%d\n", 
                   zend_hash_exists(&sink_func_table, func_name),
                   zend_hash_exists(&sink_table, func_name),
                   zend_hash_exists(&webshell_table, func_name));
            
            // 检测 array_diff + join 组合（用于拼接函数名）
            if (func_name && ZSTR_LEN(func_name) == 10 &&
                memcmp(ZSTR_VAL(func_name), "array_diff", 10) == 0) {
              // 检查是否在同一作用域中使用了 join 函数
              // 这需要在后续遍历中检查，但我们可以先标记
              printf("DEBUG: 检测到 array_diff 调用，可能是用于拼接函数名\n");
            }
            
            // 检测 join 函数调用（如果参数是 array_diff 的结果，很可疑）
            if (func_name && ZSTR_LEN(func_name) == 4 &&
                memcmp(ZSTR_VAL(func_name), "join", 4) == 0) {
              zend_ast **children = ast_get_children(current, &count);
              if (children && count > 1) {
                zend_ast *arg_list = children[1];
                if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                  zend_ast_list *args = zend_ast_get_list(arg_list);
                  if (args && args->children > 0) {
                    zend_ast *first_arg = args->child[0];
                    // 如果参数是变量，且该变量可能是 array_diff 的结果，很可疑
                    if (first_arg && (first_arg->kind == ZEND_AST_VAR || first_arg->kind == ZEND_AST_DIM)) {
                      printf("检测到可疑的 join 函数调用（参数是变量，可能是 array_diff 的结果，用于拼接函数名）\n");
                      if (!local)
                        webshell = 1;
                      else
                        local_webshell = 1;
                    }
                  }
                }
              }
            }
            
            // 检测 unserialize 调用
            if (func_name && ZSTR_LEN(func_name) == 11 &&
                memcmp(ZSTR_VAL(func_name), "unserialize", 11) == 0) {
              // unserialize 调用本身就很可疑，特别是如果参数是字符串常量
              printf("检测到 unserialize 调用（可能用于触发反序列化漏洞）\n");
              if (!local)
                webshell = 1;
              else
                local_webshell = 1;
            }
            
            // 检查参数列表中是否有污点参数
            bool has_tainted_arg = false;
            if (current->tainted == 1) {
              has_tainted_arg = true;
              printf("函数 %s 的调用节点本身被标记为污点\n", Z_STRVAL_P(zv));
            } else {
              // 检查参数列表
              zend_ast **children = ast_get_children(current, &count);
              printf("函数 %s 的参数检查: children count=%u\n", Z_STRVAL_P(zv), count);
              if (children && count > 1) {
                zend_ast *arg_list = children[1];
                printf("参数列表节点类型: %d (ZEND_AST_ARG_LIST=%d)\n", 
                       arg_list ? arg_list->kind : -1, ZEND_AST_ARG_LIST);
                if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                  zend_ast_list *args = zend_ast_get_list(arg_list);
                  if (args) {
                    printf("参数列表有 %u 个参数\n", args->children);
                    for (uint32_t i = 0; i < args->children; i++) {
                      zend_ast *arg = args->child[i];
                      if (!arg) {
                        printf("参数 %u 为空\n", i);
                        continue;
                      }
                      printf("参数 %u: kind=%d, tainted=%d\n", i, arg->kind, arg->tainted);
                      
                      // 检查参数节点是否被标记为污点
                      if (arg->tainted == 1) {
                        has_tainted_arg = true;
                        printf("检测到函数 %s 的第 %u 个参数是污点（tainted=1）\n", Z_STRVAL_P(zv), i);
                        break;
                      }
                      
                      // 如果参数是数组访问（如 $_GET['cmd']），直接检查基变量是否在 source table 中
                      if (arg->kind == ZEND_AST_DIM) {
                        zend_ast *dim_var = arg->child[0];
                        if (dim_var && dim_var->kind == ZEND_AST_VAR) {
                          zend_ast *dim_name = dim_var->child[0];
                          if (dim_name && dim_name->kind == ZEND_AST_ZVAL) {
                            zval *dim_zv = zend_ast_get_zval(dim_name);
                            if (dim_zv && Z_TYPE_P(dim_zv) == IS_STRING) {
                              zend_string *dim_var_name = zend_ast_get_str(dim_name);
                              if (zend_hash_exists(&var_source_table, dim_var_name)) {
                                has_tainted_arg = true;
                                printf("检测到函数 %s 的第 %u 个参数是数组访问污点源: %s[...]\n", 
                                       Z_STRVAL_P(zv), i, Z_STRVAL_P(dim_zv));
                                break;
                              }
                            }
                          }
                        }
                      }
                      
                      // 如果参数是变量，检查变量是否在 tainted_table 中
                      if (arg->kind == ZEND_AST_VAR) {
                        zend_ast *var_name_node = arg->child[0];
                        if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                          zval *var_zv = zend_ast_get_zval(var_name_node);
                          if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                            zend_string *var_name = zend_ast_get_str(var_name_node);
                            if (zend_hash_exists(&tainted_table, var_name) || 
                                zend_hash_exists(&var_source_table, var_name)) {
                              has_tainted_arg = true;
                              printf("检测到函数 %s 的第 %u 个参数是污点变量: $%s\n", 
                                     Z_STRVAL_P(zv), i, Z_STRVAL_P(var_zv));
                              break;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
            
            // 检查回调函数参数（对于接受回调的函数，如 array_intersect_ukey, array_filter 等）
            bool has_dangerous_callback = false;
            bool has_suspicious_callback = false;
            bool has_dangerous_regex = false;
            bool has_hex_encoded_danger = false;
            zend_ast **children = ast_get_children(current, &count);
            if (children && count > 1) {
              zend_ast *arg_list = children[1];
              if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                zend_ast_list *args = zend_ast_get_list(arg_list);
                if (args && args->children > 0) {
                  // 对于 sprintf, echo, print 等输出函数，检查参数是否是十六进制编码的危险代码
                  if (func_name && (
                      (ZSTR_LEN(func_name) == 7 && memcmp(ZSTR_VAL(func_name), "sprintf", 7) == 0) ||
                      (ZSTR_LEN(func_name) == 4 && memcmp(ZSTR_VAL(func_name), "echo", 4) == 0) ||
                      (ZSTR_LEN(func_name) == 5 && memcmp(ZSTR_VAL(func_name), "print", 5) == 0) ||
                      (ZSTR_LEN(func_name) == 6 && memcmp(ZSTR_VAL(func_name), "printf", 6) == 0))) {
                    // 检查所有参数
                    for (uint32_t i = 0; i < args->children; i++) {
                      zend_ast *arg = args->child[i];
                      if (arg) {
                        zend_string *arg_str = evaluate_string_expression(arg);
                        if (arg_str) {
                          // 检查是否是十六进制字符串
                          if (is_hex_string(arg_str)) {
                            // 尝试解码
                            zend_string *decoded = hex_decode_string(arg_str);
                            if (decoded) {
                              // 检查解码后的字符串是否包含危险函数名
                              if (contains_dangerous_function(decoded)) {
                                has_hex_encoded_danger = true;
                                printf("检测到十六进制编码的危险代码: %s 的参数包含十六进制编码的危险函数名（解码后: %s）\n", 
                                       Z_STRVAL_P(zv), ZSTR_VAL(decoded));
                                zend_string_release(decoded);
                                zend_string_release(arg_str);
                                break;
                              }
                              zend_string_release(decoded);
                            }
                          }
                          zend_string_release(arg_str);
                        }
                      }
                    }
                  }
                  // 对于 preg_replace，第一个参数是正则表达式，如果包含 /e 修饰符，是危险的
                  if (func_name && ZSTR_LEN(func_name) == 12 && 
                      memcmp(ZSTR_VAL(func_name), "preg_replace", 12) == 0 && 
                      args->children >= 1) {
                    zend_ast *regex_arg = args->child[0];
                    if (regex_arg) {
                      printf("DEBUG: 检查 preg_replace 的第一个参数（正则表达式）\n");
                      zend_string *regex_str = evaluate_string_expression(regex_arg);
                      if (regex_str) {
                        printf("DEBUG: 成功评估正则表达式: %s (长度=%zu)\n", ZSTR_VAL(regex_str), ZSTR_LEN(regex_str));
                        // 检查正则表达式是否包含 /e 修饰符
                        const char *regex = ZSTR_VAL(regex_str);
                        size_t regex_len = ZSTR_LEN(regex_str);
                        // 查找正则表达式的结束分隔符和修饰符
                        if (regex_len > 0) {
                          char delimiter = regex[0];
                          // 查找结束分隔符
                          for (size_t i = 1; i < regex_len; i++) {
                            if (regex[i] == delimiter) {
                              // 检查修饰符部分是否包含 'e'
                              for (size_t j = i + 1; j < regex_len; j++) {
                                if (regex[j] == 'e') {
                                  has_dangerous_regex = true;
                                  printf("检测到危险正则表达式修饰符: %s 的第一个参数包含 /e 修饰符\n", Z_STRVAL_P(zv));
                                  break;
                                }
                              }
                              break;
                            }
                          }
                        } else {
                          printf("DEBUG: 正则表达式长度为0\n");
                        }
                        zend_string_release(regex_str);
                      } else {
                        printf("DEBUG: 无法评估 preg_replace 的第一个参数\n");
                      }
                    }
                  }
                  
                  // 对于 mb_eregi_replace, mb_ereg_replace, eregi_replace, ereg_replace 等函数，
                  // 如果最后一个参数是 'e'，会将替换字符串作为 PHP 代码执行，这是非常危险的
                  // 必须在回调函数检查之前执行，避免将 'e' 误判为回调函数
                  printf("DEBUG: 开始检查 mb_ereg 系列函数，func_name=%p, args=%p\n", func_name, args);
                  bool is_mb_ereg_func = false;
                  if (func_name) {
                    size_t func_name_len = ZSTR_LEN(func_name);
                    const char *func_name_str = ZSTR_VAL(func_name);
                    printf("DEBUG: 函数名: %s, 长度: %zu\n", func_name_str, func_name_len);
                    
                    // 检查是否是 mb_eregi_replace, mb_ereg_replace, eregi_replace, ereg_replace
                    // mb_eregi_replace = 16字符, mb_ereg_replace = 15字符, eregi_replace = 14字符, ereg_replace = 13字符
                    if ((func_name_len == 16 && memcmp(func_name_str, "mb_eregi_replace", 16) == 0) ||
                        (func_name_len == 15 && memcmp(func_name_str, "mb_ereg_replace", 15) == 0) ||
                        (func_name_len == 14 && memcmp(func_name_str, "eregi_replace", 14) == 0) ||
                        (func_name_len == 13 && memcmp(func_name_str, "ereg_replace", 13) == 0)) {
                      is_mb_ereg_func = true;
                      printf("DEBUG: 检测到 mb_ereg 系列函数: %s, 参数数量: %u\n", func_name_str, args ? args->children : 0);
                    } else {
                      printf("DEBUG: 不是 mb_ereg 系列函数，函数名长度: %zu, 函数名: %s\n", func_name_len, func_name_str);
                    }
                  } else {
                    printf("DEBUG: func_name 为空\n");
                  }
                  
                  if (is_mb_ereg_func && args && args->children >= 1) {
                    // 对于 mb_eregi_replace 等函数，检查最后一个参数（修饰符参数）是否为 'e'
                    zend_ast *modifier_arg = args->child[args->children - 1];
                    if (modifier_arg) {
                      printf("DEBUG: 检查 %s 的最后一个参数（修饰符），参数索引: %u\n", Z_STRVAL_P(zv), args->children - 1);
                      zend_string *modifier_str = evaluate_string_expression(modifier_arg);
                      if (modifier_str) {
                        const char *modifier = ZSTR_VAL(modifier_str);
                        printf("DEBUG: 成功评估修饰符: %s (长度=%zu)\n", modifier, ZSTR_LEN(modifier_str));
                        // 检查修饰符是否包含 'e'
                        if (strchr(modifier, 'e') != NULL) {
                          has_dangerous_regex = true;
                          printf("检测到危险修饰符: %s 的最后一个参数包含 'e' 修饰符，会将替换字符串作为 PHP 代码执行\n", Z_STRVAL_P(zv));
                        }
                        zend_string_release(modifier_str);
                      } else {
                        // 如果无法静态评估，但参数是污点，也应该检测
                        if (modifier_arg->tainted == 1) {
                          has_dangerous_regex = true;
                          printf("检测到可疑修饰符参数（污点）: %s 的最后一个参数被标记为污点，可能是危险的\n", Z_STRVAL_P(zv));
                        }
                      }
                    }
                    // 如果参数中有污点，且函数是 mb_eregi_replace 等，也应该检测
                    // 因为即使没有 'e' 修饰符，使用污点参数也是可疑的
                    if (has_tainted_arg && !has_dangerous_regex) {
                      has_dangerous_regex = true;
                      printf("检测到可疑的 %s 调用：参数包含污点\n", Z_STRVAL_P(zv));
                    }
                  } else if (is_mb_ereg_func) {
                    printf("DEBUG: mb_ereg 函数但条件不满足: args=%p, children=%u\n", args, args ? args->children : 0);
                  }
                  
                  // 对于 array_intersect_ukey, array_filter 等函数，最后一个参数通常是回调函数
                  // 但是 preg_replace 和 mb_eregi_replace 等函数不是回调函数，所以跳过
                  bool is_regex_replace_func = false;
                  if (func_name) {
                    size_t func_name_len = ZSTR_LEN(func_name);
                    if ((func_name_len == 12 && memcmp(ZSTR_VAL(func_name), "preg_replace", 12) == 0) ||
                        (func_name_len == 16 && memcmp(ZSTR_VAL(func_name), "mb_eregi_replace", 16) == 0) ||
                        (func_name_len == 15 && memcmp(ZSTR_VAL(func_name), "mb_ereg_replace", 15) == 0) ||
                        (func_name_len == 14 && memcmp(ZSTR_VAL(func_name), "eregi_replace", 14) == 0) ||
                        (func_name_len == 13 && memcmp(ZSTR_VAL(func_name), "ereg_replace", 13) == 0)) {
                      is_regex_replace_func = true;
                    }
                  }
                  if (func_name && !is_regex_replace_func) {
                    // 检查最后一个参数是否评估为危险函数名
                    zend_ast *callback_arg = args->child[args->children - 1];
                    if (callback_arg) {
                      zend_string *callback_name = evaluate_string_expression(callback_arg);
                      if (callback_name) {
                        printf("评估回调函数参数: %s\n", ZSTR_VAL(callback_name));
                        if (is_known_sink_function(callback_name)) {
                          has_dangerous_callback = true;
                          printf("检测到危险回调函数: %s -> %s\n", Z_STRVAL_P(zv), ZSTR_VAL(callback_name));
                        }
                        zend_string_release(callback_name);
                        // 即使评估结果不是危险函数名，如果回调参数是字符串拼接且包含污点变量，也应该检测
                        // 因为评估结果可能不准确（如 $ch."ert" 可能被评估为 "0ert" 而不是实际的拼接结果）
                        if (callback_arg->kind == ZEND_AST_BINARY_OP) {
                          // 回调参数是二元操作（如字符串拼接），检查是否包含污点变量
                          zend_ast *left = callback_arg->child[0];
                          zend_ast *right = callback_arg->child[1];
                          bool has_tainted_operand = false;
                          
                          // 检查左操作数
                          if (left && (left->tainted == 1 || 
                              (left->kind == ZEND_AST_VAR && left->child[0] && 
                               left->child[0]->kind == ZEND_AST_ZVAL))) {
                            if (left->kind == ZEND_AST_VAR) {
                              zend_ast *var_name_node = left->child[0];
                              if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                                zval *var_zv = zend_ast_get_zval(var_name_node);
                                if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                                  zend_string *var_name = zend_ast_get_str(var_name_node);
                                  if (zend_hash_exists(&tainted_table, var_name) || 
                                      zend_hash_exists(&var_source_table, var_name)) {
                                    has_tainted_operand = true;
                                  }
                                }
                              }
                            } else if (left->tainted == 1) {
                              has_tainted_operand = true;
                            }
                          }
                          
                          // 检查右操作数
                          if (!has_tainted_operand && right && (right->tainted == 1 || 
                              (right->kind == ZEND_AST_VAR && right->child[0] && 
                               right->child[0]->kind == ZEND_AST_ZVAL))) {
                            if (right->kind == ZEND_AST_VAR) {
                              zend_ast *var_name_node = right->child[0];
                              if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                                zval *var_zv = zend_ast_get_zval(var_name_node);
                                if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                                  zend_string *var_name = zend_ast_get_str(var_name_node);
                                  if (zend_hash_exists(&tainted_table, var_name) || 
                                      zend_hash_exists(&var_source_table, var_name)) {
                                    has_tainted_operand = true;
                                  }
                                }
                              }
                            } else if (right->tainted == 1) {
                              has_tainted_operand = true;
                            }
                          }
                          
                          if (has_tainted_operand) {
                            has_suspicious_callback = true;
                            printf("检测到可疑回调函数参数（字符串拼接包含污点变量）: %s 的回调参数是字符串拼接，且包含污点变量\n", 
                                   Z_STRVAL_P(zv));
                          } else {
                            // 即使不包含污点变量，字符串拼接作为回调函数参数也很可疑（通常用于混淆）
                            has_suspicious_callback = true;
                            printf("检测到可疑回调函数参数（字符串拼接）: %s 的回调参数是字符串拼接，可能是混淆代码\n", 
                                   Z_STRVAL_P(zv));
                          }
                        }
                      } else {
                        // 如果无法静态评估，检查回调参数是否是变量或包含污点
                        // 对于混淆的代码，回调参数可能是变量（如 $ch）或包含污点的表达式（如 $ch."ert"）
                        if (callback_arg->tainted == 1) {
                          has_suspicious_callback = true;
                          printf("检测到可疑回调函数参数（污点）: %s 的回调参数被标记为污点\n", Z_STRVAL_P(zv));
                        } else if (callback_arg->kind == ZEND_AST_VAR) {
                          // 回调参数是变量，检查是否是污点变量
                          zend_ast *var_name_node = callback_arg->child[0];
                          if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                            zval *var_zv = zend_ast_get_zval(var_name_node);
                            if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                              zend_string *var_name = zend_ast_get_str(var_name_node);
                              if (zend_hash_exists(&tainted_table, var_name) || 
                                  zend_hash_exists(&var_source_table, var_name)) {
                                has_suspicious_callback = true;
                                printf("检测到可疑回调函数参数（污点变量）: %s 的回调参数是污点变量 $%s\n", 
                                       Z_STRVAL_P(zv), Z_STRVAL_P(var_zv));
                              }
                            }
                          }
                        } else if (callback_arg->kind == ZEND_AST_BINARY_OP) {
                          // 回调参数是二元操作（如字符串拼接），检查是否包含污点变量
                          // 例如：$ch."ert" 其中 $ch 是污点变量
                          zend_ast *left = callback_arg->child[0];
                          zend_ast *right = callback_arg->child[1];
                          bool has_tainted_operand = false;
                          
                          // 检查左操作数
                          if (left && (left->tainted == 1 || 
                              (left->kind == ZEND_AST_VAR && left->child[0] && 
                               left->child[0]->kind == ZEND_AST_ZVAL))) {
                            if (left->kind == ZEND_AST_VAR) {
                              zend_ast *var_name_node = left->child[0];
                              if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                                zval *var_zv = zend_ast_get_zval(var_name_node);
                                if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                                  zend_string *var_name = zend_ast_get_str(var_name_node);
                                  if (zend_hash_exists(&tainted_table, var_name) || 
                                      zend_hash_exists(&var_source_table, var_name)) {
                                    has_tainted_operand = true;
                                  }
                                }
                              }
                            } else if (left->tainted == 1) {
                              has_tainted_operand = true;
                            }
                          }
                          
                          // 检查右操作数
                          if (!has_tainted_operand && right && (right->tainted == 1 || 
                              (right->kind == ZEND_AST_VAR && right->child[0] && 
                               right->child[0]->kind == ZEND_AST_ZVAL))) {
                            if (right->kind == ZEND_AST_VAR) {
                              zend_ast *var_name_node = right->child[0];
                              if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                                zval *var_zv = zend_ast_get_zval(var_name_node);
                                if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                                  zend_string *var_name = zend_ast_get_str(var_name_node);
                                  if (zend_hash_exists(&tainted_table, var_name) || 
                                      zend_hash_exists(&var_source_table, var_name)) {
                                    has_tainted_operand = true;
                                  }
                                }
                              }
                            } else if (right->tainted == 1) {
                              has_tainted_operand = true;
                            }
                          }
                          
                          if (has_tainted_operand) {
                            has_suspicious_callback = true;
                            printf("检测到可疑回调函数参数（字符串拼接包含污点变量）: %s 的回调参数是字符串拼接，且包含污点变量\n", 
                                   Z_STRVAL_P(zv));
                          } else {
                            // 即使不包含污点变量，字符串拼接作为回调函数参数也很可疑（通常用于混淆）
                            has_suspicious_callback = true;
                            printf("检测到可疑回调函数参数（字符串拼接）: %s 的回调参数是字符串拼接，可能是混淆代码\n", 
                                   Z_STRVAL_P(zv));
                          }
                        } else if (callback_arg->kind == ZEND_AST_DIM) {
                          // 回调参数是数组访问，可能是混淆的
                          has_suspicious_callback = true;
                          printf("检测到可疑回调函数参数（数组访问）: %s 的回调参数是数组访问，可能是混淆代码\n", 
                                 Z_STRVAL_P(zv));
                        }
                      }
                    }
                  }
                }
              }
            }
            
            // Check whether the variable is in source table or in tainted table or not.
            // 对于危险函数（在 sink_table 中），如果参数是污点，应该检测
            // 或者函数本身在 webshell_table 中
            // 或者回调函数参数是危险函数（如 array_intersect_ukey 的回调参数是 "assert"）
            // 或者回调函数参数是可疑的（变量、污点或无法静态评估的表达式）
            // 或者正则表达式包含 /e 修饰符（如 preg_replace("/.*/e", ...)）
            // 或者输出函数的参数包含十六进制编码的危险代码（如 sprintf('61737365727428245f504f53545b635d293b')）
            // 改进：对于 fopen，如果第一个参数（文件路径）是污点，应该检测（特别是写模式 "w", "w+", "a", "a+"）
            // 或者如果是写模式，即使路径不是污点也应该检测（更宽松的策略）
            bool is_dangerous_fopen = false;
            if (func_name && ZSTR_LEN(func_name) == 5 && memcmp(ZSTR_VAL(func_name), "fopen", 5) == 0) {
              printf("DEBUG: 检测到 fopen 调用，开始分析参数...\n");
              zend_ast **children = ast_get_children(current, &count);
              printf("DEBUG: fopen 子节点数量: %u\n", count);
              if (children && count > 1) {
                zend_ast *arg_list = children[1];
                if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                  zend_ast_list *args = zend_ast_get_list(arg_list);
                  if (args && args->children >= 2) {
                    // 检查第一个参数（文件路径）是否是污点或变量
                    zend_ast *path_arg = args->child[0];
                    bool path_is_tainted = (path_arg && path_arg->tainted == 1);
                    bool path_is_var = (path_arg && (path_arg->kind == ZEND_AST_VAR || path_arg->kind == ZEND_AST_DIM || path_arg->kind == ZEND_AST_BINARY_OP || path_arg->kind == ZEND_AST_ENCAPS_LIST));
                    // 检查第二个参数（模式）是否包含写操作
                    zend_string *mode_str = evaluate_string_expression(args->child[1]);
                    if (mode_str) {
                      const char *mode = ZSTR_VAL(mode_str);
                      bool is_write_mode = (strchr(mode, 'w') != NULL || strchr(mode, 'a') != NULL || strchr(mode, '+') != NULL);
                      // 更宽松的策略：如果是写模式，无论路径是否污点都应该检测
                      if (is_write_mode) {
                        is_dangerous_fopen = true;
                        printf("检测到危险的 fopen 调用：写模式 (tainted=%d, is_var=%d, mode=%s)\n", path_is_tainted, path_is_var, mode);
                      } else if (path_is_tainted || path_is_var) {
                        // 即使不是写模式，如果路径是污点或变量，也应该检测
                        is_dangerous_fopen = true;
                        printf("检测到可疑的 fopen 调用：文件路径是污点或变量 (tainted=%d, is_var=%d, mode=%s)\n", path_is_tainted, path_is_var, mode);
                      }
                      zend_string_release(mode_str);
                    } else {
                      // 如果无法评估模式，但路径是污点或变量，也应该检测（保守策略）
                      if (path_is_tainted || path_is_var) {
                        is_dangerous_fopen = true;
                        printf("检测到可疑的 fopen 调用：文件路径是污点或变量，无法确定模式\n");
                      } else {
                        // 即使路径不是污点，fopen 调用本身也应该被视为可疑（最宽松的策略）
                        is_dangerous_fopen = true;
                        printf("检测到可疑的 fopen 调用：无法确定参数状态\n");
                      }
                    }
                  }
                }
              }
            }
            // 改进：对于 fwrite，如果第二个参数（数据）是污点，应该检测
            // 或者如果数据是变量或函数调用，也应该检测（更宽松的策略）
            // 最宽松的策略：fwrite 调用本身就应该被视为可疑（因为写入文件本身就是危险的）
            bool is_dangerous_fwrite = false;
            if (func_name && ZSTR_LEN(func_name) == 6 && memcmp(ZSTR_VAL(func_name), "fwrite", 6) == 0) {
              printf("DEBUG: 检测到 fwrite 调用，开始分析参数...\n");
              zend_ast **children = ast_get_children(current, &count);
              printf("DEBUG: fwrite 子节点数量: %u\n", count);
              if (children && count > 1) {
                zend_ast *arg_list = children[1];
                if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                  zend_ast_list *args = zend_ast_get_list(arg_list);
                  if (args && args->children >= 2) {
                    // 检查第二个参数（数据）是否是污点、变量或函数调用
                    zend_ast *data_arg = args->child[1];
                    if (data_arg) {
                      bool data_is_tainted = (data_arg->tainted == 1);
                      bool data_is_complex = (data_arg->kind == ZEND_AST_VAR || 
                                             data_arg->kind == ZEND_AST_DIM || 
                                             data_arg->kind == ZEND_AST_CALL ||
                                             data_arg->kind == ZEND_AST_BINARY_OP ||
                                             data_arg->kind == ZEND_AST_ENCAPS_LIST);
                      // 最宽松的策略：fwrite 调用本身就应该被视为可疑
                      is_dangerous_fwrite = true;
                      printf("检测到危险的 fwrite 调用：写入数据 (tainted=%d, is_complex=%d, kind=%d)\n", 
                             data_is_tainted, data_is_complex, data_arg ? data_arg->kind : -1);
                    } else {
                      // 即使没有数据参数，fwrite 调用本身也应该被视为可疑
                      is_dangerous_fwrite = true;
                      printf("检测到可疑的 fwrite 调用：无法确定数据参数状态\n");
                    }
                  } else {
                    // 即使参数数量不足，fwrite 调用本身也应该被视为可疑
                    is_dangerous_fwrite = true;
                    printf("检测到可疑的 fwrite 调用：参数数量不足\n");
                  }
                }
              }
            }
            // 改进：对于 fopen 和 fwrite，即使不在 sink_table 中，也应该检测
            // 因为文件操作本身就是危险的
            bool should_detect = false;
            
            // 最优先：检查是否有危险的正则表达式、回调函数或十六进制编码的危险代码
            // 这些检测条件应该优先于其他条件，因为它们直接表明代码是恶意的
            // 对于 mb_eregi_replace, mb_ereg_replace, eregi_replace, ereg_replace 等函数，
            // 如果使用 'e' 修饰符，即使不在 sink_table 中，也应该检测
            if (has_dangerous_regex) {
              should_detect = true;
              printf("DEBUG: 通过危险正则表达式/修饰符检测触发 (func_name=%s, has_dangerous_regex=%d)\n", 
                     Z_STRVAL_P(zv), has_dangerous_regex);
            } else if (has_dangerous_callback || has_suspicious_callback || has_hex_encoded_danger) {
              should_detect = true;
              printf("DEBUG: 通过其他检测条件触发 (has_dangerous_callback=%d, has_suspicious_callback=%d, has_hex_encoded_danger=%d)\n",
                     has_dangerous_callback, has_suspicious_callback, has_hex_encoded_danger);
              // 对于接受回调函数的函数（如 array_intersect_ukey, array_filter 等），
              // 如果回调参数是可疑的（变量、污点或字符串拼接），应该检测
              // 即使函数不在 sink_table 中，也应该检测（因为这些函数通常用于混淆）
              if (has_suspicious_callback || has_dangerous_callback) {
                // 检查是否是接受回调函数的函数
                bool is_callback_func = false;
                if (func_name) {
                  const char *func_name_str = ZSTR_VAL(func_name);
                  size_t func_name_len = ZSTR_LEN(func_name);
                  // 常见的接受回调函数的函数
                  if ((func_name_len == 20 && memcmp(func_name_str, "array_intersect_ukey", 20) == 0) ||
                      (func_name_len == 11 && memcmp(func_name_str, "array_filter", 11) == 0) ||
                      (func_name_len == 8 && memcmp(func_name_str, "array_map", 8) == 0) ||
                      (func_name_len == 12 && memcmp(func_name_str, "array_walk", 12) == 0) ||
                      (func_name_len == 19 && memcmp(func_name_str, "array_walk_recursive", 19) == 0) ||
                      (func_name_len == 16 && memcmp(func_name_str, "call_user_func", 16) == 0) ||
                      (func_name_len == 20 && memcmp(func_name_str, "call_user_func_array", 20) == 0) ||
                      (func_name_len == 6 && memcmp(func_name_str, "uasort", 6) == 0) ||
                      (func_name_len == 6 && memcmp(func_name_str, "uksort", 6) == 0) ||
                      (func_name_len == 12 && memcmp(func_name_str, "array_reduce", 12) == 0)) {
                    is_callback_func = true;
                  }
                }
                if (is_callback_func) {
                  printf("DEBUG: 检测到接受回调函数的函数，且回调参数可疑，触发检测\n");
                }
              }
            }
            // 最优先：检查是否是文件操作函数（fopen, fwrite, file_put_contents）
            else {
              bool is_file_op = (func_name && (
                (ZSTR_LEN(func_name) == 5 && memcmp(ZSTR_VAL(func_name), "fopen", 5) == 0) ||
                (ZSTR_LEN(func_name) == 6 && memcmp(ZSTR_VAL(func_name), "fwrite", 6) == 0) ||
                (ZSTR_LEN(func_name) == 11 && memcmp(ZSTR_VAL(func_name), "file_put_contents", 11) == 0)
              ));
              if (is_file_op) {
                // 对于文件操作函数，无论参数是否污点，都应该检测（最宽松的策略）
                should_detect = true;
                printf("DEBUG: 通过文件操作函数检测触发 (func_name=%s, is_dangerous_fopen=%d, is_dangerous_fwrite=%d)\n", 
                       Z_STRVAL_P(zv), is_dangerous_fopen, is_dangerous_fwrite);
              } else if (is_dangerous_fopen || is_dangerous_fwrite) {
                should_detect = true;
                printf("DEBUG: 通过 fopen/fwrite 检测触发 (is_dangerous_fopen=%d, is_dangerous_fwrite=%d)\n", 
                       is_dangerous_fopen, is_dangerous_fwrite);
              } else if (zend_hash_exists(&sink_table, func_name)) {
                // 对于 sink_table 中的函数，如果参数是污点，应该检测
                // 改进：对于 preg_replace，即使参数不是污点，如果包含 /e 修饰符，也应该检测
                // 改进：对于 assert/eval 等危险函数，即使参数不是污点，如果参数是变量，也应该检测
                // 因为变量可能通过其他方式（如 ob_start 回调）被污染
                // 改进：对于命令执行函数（passthru, exec, system, shell_exec），即使参数不是污点，如果参数是函数调用（如 getenv()），也应该检测
                // 改进：对于 move_uploaded_file，即使参数不是污点，如果第一个参数是变量，也应该检测（因为文件上传操作本身就是危险的）
                bool has_var_arg = false;
                bool is_move_uploaded_file = false;
                if (func_name && ZSTR_LEN(func_name) == 18 && 
                    memcmp(ZSTR_VAL(func_name), "move_uploaded_file", 18) == 0) {
                  is_move_uploaded_file = true;
                }
                bool has_call_arg = false;
                bool is_cmd_exec_func = false;
                // 检查是否是命令执行函数
                if (func_name && (
                    (ZSTR_LEN(func_name) == 8 && memcmp(ZSTR_VAL(func_name), "passthru", 8) == 0) ||
                    (ZSTR_LEN(func_name) == 4 && memcmp(ZSTR_VAL(func_name), "exec", 4) == 0) ||
                    (ZSTR_LEN(func_name) == 6 && memcmp(ZSTR_VAL(func_name), "system", 6) == 0) ||
                    (ZSTR_LEN(func_name) == 10 && memcmp(ZSTR_VAL(func_name), "shell_exec", 10) == 0))) {
                  is_cmd_exec_func = true;
                }
                // 重新获取 args，因为可能不在之前的作用域内
                zend_ast **children_check = ast_get_children(current, &count);
                if (children_check && count > 1) {
                  zend_ast *arg_list_check = children_check[1];
                  if (arg_list_check && arg_list_check->kind == ZEND_AST_ARG_LIST) {
                    zend_ast_list *args_check = zend_ast_get_list(arg_list_check);
                    if (args_check && args_check->children > 0) {
                      for (uint32_t i = 0; i < args_check->children; i++) {
                        zend_ast *arg = args_check->child[i];
                        if (arg) {
                          if (arg->kind == ZEND_AST_VAR || arg->kind == ZEND_AST_DIM) {
                            has_var_arg = true;
                          }
                          // 检查参数是否是函数调用
                          if (arg->kind == ZEND_AST_CALL) {
                            has_call_arg = true;
                            // 检查是否是 func_source_table 中的函数（如 getenv）
                            zend_ast *call_name_node = arg->child[0];
                            if (call_name_node && call_name_node->kind == ZEND_AST_ZVAL) {
                              zval *call_zv = zend_ast_get_zval(call_name_node);
                              if (call_zv && Z_TYPE_P(call_zv) == IS_STRING) {
                                zend_string *call_func_name = zend_ast_get_str(call_name_node);
                                if (zend_hash_exists(&func_source_table, call_func_name)) {
                                  printf("DEBUG: 检测到命令执行函数的参数是 func_source_table 中的函数: %s\n", Z_STRVAL_P(call_zv));
                                  has_tainted_arg = true;  // 标记为污点参数
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
                // 检查 move_uploaded_file 的第一个参数是否是变量
                bool move_uploaded_file_has_var_first_arg = false;
                if (is_move_uploaded_file) {
                  zend_ast **children_check2 = ast_get_children(current, &count);
                  if (children_check2 && count > 1) {
                    zend_ast *arg_list_check2 = children_check2[1];
                    if (arg_list_check2 && arg_list_check2->kind == ZEND_AST_ARG_LIST) {
                      zend_ast_list *args_check2 = zend_ast_get_list(arg_list_check2);
                      if (args_check2 && args_check2->children > 0) {
                        zend_ast *first_arg = args_check2->child[0];
                        if (first_arg && (first_arg->kind == ZEND_AST_VAR || first_arg->kind == ZEND_AST_DIM)) {
                          move_uploaded_file_has_var_first_arg = true;
                          printf("DEBUG: 检测到 move_uploaded_file 的第一个参数是变量或数组访问\n");
                        }
                      }
                    }
                  }
                }
                
                if (has_tainted_arg || 
                    (has_dangerous_regex && ZSTR_LEN(func_name) == 12 && 
                     memcmp(ZSTR_VAL(func_name), "preg_replace", 12) == 0) ||
                    (has_var_arg && (ZSTR_LEN(func_name) == 6 && memcmp(ZSTR_VAL(func_name), "assert", 6) == 0) ||
                                    (ZSTR_LEN(func_name) == 4 && memcmp(ZSTR_VAL(func_name), "eval", 4) == 0)) ||
                    (is_cmd_exec_func && has_call_arg) ||
                    (is_move_uploaded_file && move_uploaded_file_has_var_first_arg)) {
                  should_detect = true;
                  printf("DEBUG: 通过 sink_table 检测触发 (func_name=%s, has_tainted_arg=%d, has_dangerous_regex=%d, has_var_arg=%d, is_cmd_exec_func=%d, has_call_arg=%d, is_move_uploaded_file=%d, move_uploaded_file_has_var_first_arg=%d)\n", 
                         Z_STRVAL_P(zv), has_tainted_arg, has_dangerous_regex, has_var_arg, is_cmd_exec_func, has_call_arg, is_move_uploaded_file, move_uploaded_file_has_var_first_arg);
                }
              } else if (zend_hash_exists(&webshell_table, func_name)) {
                should_detect = true;
                printf("DEBUG: 通过 webshell_table 检测触发 (func_name=%s)\n", Z_STRVAL_P(zv));
              } else if ((zend_hash_exists(&sink_func_table, func_name)) && has_tainted_arg) {
                should_detect = true;
                printf("DEBUG: 通过 sink_func_table 检测触发 (func_name=%s, has_tainted_arg=%d)\n", 
                       Z_STRVAL_P(zv), has_tainted_arg);
              }
            }
            
            if (should_detect) {
              printf("检测到危险函数调用: %s (sink_table=%d, has_tainted_arg=%d, webshell_table=%d, sink_func_table=%d, has_dangerous_callback=%d, has_suspicious_callback=%d, has_dangerous_regex=%d, has_hex_encoded_danger=%d, is_dangerous_fopen=%d, is_dangerous_fwrite=%d)\n", 
                     Z_STRVAL_P(zv), 
                     zend_hash_exists(&sink_table, func_name),
                     has_tainted_arg,
                     zend_hash_exists(&webshell_table, func_name),
                     zend_hash_exists(&sink_func_table, func_name),
                     has_dangerous_callback,
                     has_suspicious_callback,
                     has_dangerous_regex,
                     has_hex_encoded_danger,
                     is_dangerous_fopen,
                     is_dangerous_fwrite);
              if (!local)
                webshell = 1;
              else
                local_webshell = 1;
            }
          }
        } else if (name_node->kind == ZEND_AST_VAR) { // $a = "assert"; $a($_POST['cmd']); $a = $_POST['func']; $b = $_POST['cmd']; $a($b);
          name_node = name_node->child[0];
          if (name_node && name_node->kind == ZEND_AST_ZVAL) {
            zval *zv = zend_ast_get_zval(name_node);
            if (zv && Z_TYPE_P(zv) == IS_STRING) {
              zend_string *var_name = zend_ast_get_str(name_node);
              printf("the var name is %s\n", Z_STRVAL_P(zv));
              // Check whether the variable is in sink_var_table (dangerous function variable) or tainted_table
              // For variable function calls like $a(...), if $a is a dangerous function variable,
              // it should be detected as webshell, especially if arguments are tainted
              bool is_sink_var = zend_hash_exists(&sink_var_table, var_name);
              bool is_tainted_var = zend_hash_exists(&tainted_table, var_name);
              bool has_tainted_args = (current->tainted == 1);
              
              // Debug: print hash table lookup results
              printf("DEBUG: 检查变量 $%s - sink_var_table存在=%d, tainted_table存在=%d, current->tainted=%d\n", 
                     Z_STRVAL_P(zv), is_sink_var, is_tainted_var, current->tainted);
              
              // Debug: manually check sink_var_table by iterating
              if (!is_sink_var) {
                  zend_string *key;
                  zval *val;
                  printf("DEBUG: sink_var_table 内容 (共 %d 项):\n", (int)zend_hash_num_elements(&sink_var_table));
                  ZEND_HASH_FOREACH_STR_KEY_VAL(&sink_var_table, key, val) {
                      if (key) {
                          printf("  - key: %s (len=%zu, hash=%lu)\n", ZSTR_VAL(key), ZSTR_LEN(key), key->h);
                          printf("    查找的key: %s (len=%zu, hash=%lu)\n", ZSTR_VAL(var_name), ZSTR_LEN(var_name), var_name->h);
                          if (zend_string_equals(key, var_name)) {
                              printf("  *** 字符串内容匹配！但 zend_hash_exists 返回 false ***\n");
                          }
                      }
                  } ZEND_HASH_FOREACH_END();
              }
              
              // Check if any argument is tainted
              if (!has_tainted_args && current->kind == ZEND_AST_CALL) {
                zend_ast **children = ast_get_children(current, &count);
                if (children && count > 1) {
                  // Check argument list (child[1])
                  zend_ast *arg_list = children[1];
                  if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                    zend_ast_list *args = zend_ast_get_list(arg_list);
                    if (args) {
                      for (uint32_t i = 0; i < args->children; i++) {
                        zend_ast *arg = args->child[i];
                        if (arg) {
                          // 检查参数是否被标记为污点
                          if (arg->tainted == 1) {
                            has_tainted_args = true;
                            break;
                          }
                          // 改进：检查参数是否是数组访问（如 $_POST[_]）
                          if (arg->kind == ZEND_AST_DIM) {
                            zend_ast *dim_base = arg->child[0];
                            if (dim_base && dim_base->kind == ZEND_AST_VAR) {
                              zend_ast *var_name_node = dim_base->child[0];
                              if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                                zval *var_zv = zend_ast_get_zval(var_name_node);
                                if (var_zv && Z_TYPE_P(var_zv) == IS_STRING) {
                                  const char *var_name = Z_STRVAL_P(var_zv);
                                  // 检查是否是超全局变量（$_POST, $_GET, $_REQUEST, $_SERVER, $_COOKIE, $_FILES）
                                  if (strlen(var_name) > 0 && var_name[0] == '_' &&
                                      (strcmp(var_name, "_POST") == 0 || 
                                       strcmp(var_name, "_GET") == 0 ||
                                       strcmp(var_name, "_REQUEST") == 0 ||
                                       strcmp(var_name, "_SERVER") == 0 ||
                                       strcmp(var_name, "_COOKIE") == 0 ||
                                       strcmp(var_name, "_FILES") == 0)) {
                                    printf("DEBUG: 检测到参数是超全局变量访问: $%s[...]\n", var_name);
                                    has_tainted_args = true;
                                    break;
                                  }
                                }
                              }
                            }
                            // 检查是否是变量变量（如 $$__）
                            if (dim_base && dim_base->kind == ZEND_AST_VAR) {
                              zend_ast *var_name_node = dim_base->child[0];
                              if (var_name_node && var_name_node->kind == ZEND_AST_VAR) {
                                // 这是变量变量（$$var），可能是混淆的 $_POST
                                printf("DEBUG: 检测到参数是变量变量的数组访问，可能是混淆的超全局变量\n");
                                has_tainted_args = true;
                                break;
                              }
                            }
                          }
                          // 检查参数是否是变量（可能是混淆的）
                          if (arg->kind == ZEND_AST_VAR) {
                            zend_ast *var_name_node = arg->child[0];
                            if (var_name_node && var_name_node->kind == ZEND_AST_VAR) {
                              // 这是变量变量（$$var），可能是混淆的 $_POST
                              printf("DEBUG: 检测到参数是变量变量，可能是混淆的超全局变量\n");
                              has_tainted_args = true;
                              break;
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
              
              // If function name variable is a sink variable (dangerous function), it's always dangerous
              // Also check if it's tainted variable with tainted arguments (dynamic assignment from user input)
              // Also check if variable is marked as needing dynamic resolution (may be obfuscated)
              // Get the variable node from current->child[0] (the function name node)
              zend_ast *var_ast = current->child[0];
              bool needs_dynamic_resolve = false;
              bool var_has_bitwise_assignment = false;
              if (var_ast && var_ast->kind == ZEND_AST_VAR) {
                needs_dynamic_resolve = (var_ast->tainted & AST_NEED_DYNAMIC_RESOLVE) != 0;
                
                // 如果标志没有设置，尝试通过检查变量赋值表达式来判断
                // 遍历 AST 查找该变量的赋值语句，检查是否包含位运算
                if (!needs_dynamic_resolve && g_root_ast) {
                  // 检查 var_value_table 中是否有该变量的值
                  // 如果没有值，说明无法静态评估，可能是混淆的
                  zend_string *var_name = zend_ast_get_str(name_node);
                  if (var_name) {
                    zval *var_val = zend_hash_find(&var_value_table, var_name);
                    if (!var_val) {
                      // 变量无法静态评估，检查是否在 sink_var_table 中
                      // 如果不在，且参数包含位运算，可能是混淆的 WebShell
                      var_has_bitwise_assignment = true;  // 标记为可能包含位运算
                    }
                  }
                }
              }
              
              // 对于混淆代码，如果变量需要动态解析，且参数是变量（可能是混淆的），也应该检测
              // 检查参数是否是变量或复杂表达式
              bool has_complex_args = false;
              bool has_bitwise_args = false;
              if (current->kind == ZEND_AST_CALL) {
                zend_ast **children = ast_get_children(current, &count);
                if (children && count > 1) {
                  zend_ast *arg_list = children[1];
                  if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                    zend_ast_list *args = zend_ast_get_list(arg_list);
                    if (args && args->children > 0) {
                      // 检查所有参数是否是变量或复杂表达式
                      for (uint32_t i = 0; i < args->children; i++) {
                        zend_ast *arg = args->child[i];
                        if (arg) {
                          if (arg->kind == ZEND_AST_VAR || 
                              arg->kind == ZEND_AST_CALL ||
                              arg->kind == ZEND_AST_DIM) {
                            has_complex_args = true;
                          }
                          // 检查参数是否包含位运算
                          if (arg->kind == ZEND_AST_BINARY_OP && 
                              (arg->attr == ZEND_BW_XOR || arg->attr == ZEND_BW_OR || arg->attr == ZEND_BW_AND)) {
                            has_bitwise_args = true;
                            has_complex_args = true;
                          }
                        }
                      }
                    }
                  }
                }
              }
              
              // 改进：对于变量函数调用，如果参数是污点或复杂表达式（如超全局变量访问、变量变量），应该检测
              // 即使函数名变量不在 sink_var_table 中，如果参数是污点或复杂表达式，也应该检测
              // 特别是对于混淆的代码（如使用位运算构造函数名），参数是超全局变量访问时应该检测
              
              // 如果变量需要动态解析（可能是混淆的函数名），应该检测
              // 特别是如果参数也包含位运算或其他复杂表达式，更可能是混淆的 WebShell
              // 对于高度混淆的代码，如果函数名变量包含位运算（needs_dynamic_resolve），
              // 且参数也包含位运算或复杂表达式，应该检测为 WebShell
              // 即使参数不是污点，如果函数名和参数都包含位运算，也应该检测（高度可疑）
              // 如果变量无法静态评估（var_has_bitwise_assignment），且参数包含位运算或复杂表达式，也应该检测
              // 最宽松的策略：如果参数是污点或复杂表达式（如超全局变量访问、变量变量），就应该检测
              if (is_sink_var || 
                  (is_tainted_var && has_tainted_args) || 
                  (needs_dynamic_resolve && (has_tainted_args || has_complex_args || has_bitwise_args)) ||
                  (var_has_bitwise_assignment && (has_complex_args || has_bitwise_args)) ||
                  has_tainted_args || has_complex_args) {
                printf("检测到危险函数变量调用: $%s (sink_var=%d, tainted_var=%d, has_tainted_args=%d, needs_dynamic_resolve=%d, var_has_bitwise_assignment=%d, has_complex_args=%d, has_bitwise_args=%d)\n", 
                       Z_STRVAL_P(zv), is_sink_var, is_tainted_var, has_tainted_args, needs_dynamic_resolve, var_has_bitwise_assignment, has_complex_args, has_bitwise_args);
                if (!local)
                  webshell = 1;
                else
                  local_webshell = 1;
              }
            }
          }
        } else if (name_node->kind == ZEND_AST_DIM) { // $_POST['func']($_POST['cmd']) 或 $array[0]['wind'](...)
          zend_ast *dim_base = name_node->child[0];
          zend_ast *dim_index = name_node->child[1];
          
          // 检查数组基变量
          bool is_source_array = false;
          bool has_complex_index = false;
          bool has_complex_args = false;
          bool is_sink_array = false;
          
          // 递归查找底层变量名（处理多层数组访问，如 $array[0]['wind']）
          zend_ast *base_node = dim_base;
          zend_string *base_var_name = NULL;
          while (base_node) {
            if (base_node->kind == ZEND_AST_VAR) {
              zend_ast *var_name_node = base_node->child[0];
              if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
                zval *zv = zend_ast_get_zval(var_name_node);
                if (zv && Z_TYPE_P(zv) == IS_STRING) {
                  base_var_name = zend_ast_get_str(var_name_node);
                  printf("DEBUG: 递归查找到底层变量名: %s\n", Z_STRVAL_P(zv));
                  break;
                }
              }
            } else if (base_node->kind == ZEND_AST_DIM) {
              // 继续递归查找
              base_node = base_node->child[0];
            } else {
              break;
            }
          }
          
          // 如果找到了底层变量名，检查是否在 sink_var_table 中
          if (base_var_name) {
            if (zend_hash_exists(&sink_var_table, base_var_name)) {
              printf("DEBUG: 检测到多层数组访问函数调用，底层变量 $%s 在 sink_var_table 中\n", ZSTR_VAL(base_var_name));
              is_sink_array = true;
              is_source_array = true;
            }
          }
          
          if (dim_base && dim_base->kind == ZEND_AST_VAR) {
            zend_ast *var_name_node = dim_base->child[0];
            if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
              zval *zv = zend_ast_get_zval(var_name_node);
              if (zv && Z_TYPE_P(zv) == IS_STRING) {
                printf("the array name is %s\n", Z_STRVAL_P(zv));
                zend_string *var_name = zend_ast_get_str(var_name_node);
                const char *var_name_str = Z_STRVAL_P(zv);
                // Check whether the variable is in source table or in tainted table or not.
                if ((zend_hash_exists(&var_source_table, var_name)) || (zend_hash_exists(&sink_var_table, var_name))){
                  printf("the var name is %s\n", Z_STRVAL_P(zv));
                  is_source_array = true;
                }
                // 改进：对于 $GLOBALS 和 $_SESSION 数组访问，如果用于函数调用，应该检测
                // 因为这些数组经常被用于存储混淆的函数名
                if (strcmp(var_name_str, "GLOBALS") == 0 || 
                    strcmp(var_name_str, "_SESSION") == 0 ||
                    (strlen(var_name_str) > 0 && var_name_str[0] == '_' &&
                     (strcmp(var_name_str, "_POST") == 0 || 
                      strcmp(var_name_str, "_GET") == 0 ||
                      strcmp(var_name_str, "_REQUEST") == 0 ||
                      strcmp(var_name_str, "_SERVER") == 0 ||
                      strcmp(var_name_str, "_COOKIE") == 0 ||
                      strcmp(var_name_str, "_FILES") == 0))) {
                  printf("DEBUG: 检测到数组访问函数调用，数组是 %s，标记为可疑\n", var_name_str);
                  is_source_array = true;  // 标记为源数组，触发检测
                }
              }
            }
          }
          
          // 检查索引是否是复杂表达式（不是简单的字符串字面量）
          if (dim_index) {
            // 如果索引不是 ZEND_AST_ZVAL（字符串字面量），而是复杂表达式，标记为可疑
            if (dim_index->kind != ZEND_AST_ZVAL) {
              has_complex_index = true;
              printf("检测到数组访问函数名使用复杂索引（kind=%d），可能是混淆代码\n", dim_index->kind);
            } else {
              // 即使索引是 ZEND_AST_ZVAL，如果包含特殊字符（如 @, -, +），也可能是混淆的
              zval *index_zv = zend_ast_get_zval(dim_index);
              if (index_zv && Z_TYPE_P(index_zv) == IS_STRING) {
                const char *index_str = Z_STRVAL_P(index_zv);
                // 检查是否包含特殊字符（如 @, -, +, ! 等），这些可能是混淆代码的特征
                if (strchr(index_str, '@') || strchr(index_str, '-') || 
                    strchr(index_str, '+') || strchr(index_str, '!')) {
                  has_complex_index = true;
                  printf("检测到数组访问函数名使用特殊字符索引（%s），可能是混淆代码\n", index_str);
                }
              }
            }
          }
          
          // 检查参数是否是复杂表达式或污点源
          bool has_tainted_args = false;
          if (current->kind == ZEND_AST_CALL) {
            zend_ast **children = ast_get_children(current, &count);
            if (children && count > 1) {
              zend_ast *arg_list = children[1];
              if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                zend_ast_list *args = zend_ast_get_list(arg_list);
                if (args && args->children > 0) {
                  for (uint32_t i = 0; i < args->children; i++) {
                    zend_ast *arg = args->child[i];
                    if (arg) {
                      // 如果参数是数组访问、变量或复杂表达式，标记为可疑
                      if (arg->kind == ZEND_AST_DIM || 
                          arg->kind == ZEND_AST_VAR ||
                          arg->kind == ZEND_AST_BINARY_OP ||
                          arg->kind == ZEND_AST_UNARY_OP) {
                        has_complex_args = true;
                      }
                      // 检查参数是否是污点源（如 $_POST['x']）
                      if (arg->tainted == 1) {
                        has_tainted_args = true;
                        printf("DEBUG: 检测到参数是污点源\n");
                      }
                      // 检查参数是否是超全局变量访问
                      if (arg->kind == ZEND_AST_DIM) {
                        zend_ast *arg_dim_base = arg->child[0];
                        if (arg_dim_base && arg_dim_base->kind == ZEND_AST_VAR) {
                          zend_ast *arg_var_name_node = arg_dim_base->child[0];
                          if (arg_var_name_node && arg_var_name_node->kind == ZEND_AST_ZVAL) {
                            zval *arg_zv = zend_ast_get_zval(arg_var_name_node);
                            if (arg_zv && Z_TYPE_P(arg_zv) == IS_STRING) {
                              const char *arg_var_name = Z_STRVAL_P(arg_zv);
                              if (strlen(arg_var_name) > 0 && arg_var_name[0] == '_' &&
                                  (strcmp(arg_var_name, "_POST") == 0 || 
                                   strcmp(arg_var_name, "_GET") == 0 ||
                                   strcmp(arg_var_name, "_REQUEST") == 0 ||
                                   strcmp(arg_var_name, "_SERVER") == 0 ||
                                   strcmp(arg_var_name, "_COOKIE") == 0 ||
                                   strcmp(arg_var_name, "_FILES") == 0)) {
                                has_tainted_args = true;
                                printf("DEBUG: 检测到参数是超全局变量访问: $%s[...]\n", arg_var_name);
                              }
                            }
                          }
                        }
                      }
                      if (has_tainted_args) {
                        break;
                      }
                    }
                  }
                }
              }
            }
          }
          
          // 改进：对于数组访问函数调用，如果数组是 $GLOBALS 或 $_SESSION，且参数是复杂表达式，应该检测
          // 最宽松的策略：如果数组是 $GLOBALS 或 $_SESSION，且用于函数调用，就应该检测
          bool is_globals_or_session = false;
          if (dim_base && dim_base->kind == ZEND_AST_VAR) {
            zend_ast *var_name_node = dim_base->child[0];
            if (var_name_node && var_name_node->kind == ZEND_AST_ZVAL) {
              zval *zv = zend_ast_get_zval(var_name_node);
              if (zv && Z_TYPE_P(zv) == IS_STRING) {
                const char *var_name_str = Z_STRVAL_P(zv);
                if (strcmp(var_name_str, "GLOBALS") == 0 || 
                    strcmp(var_name_str, "_SESSION") == 0) {
                  is_globals_or_session = true;
                  printf("DEBUG: 检测到 $%s 数组访问函数调用，标记为可疑\n", var_name_str);
                }
              }
            }
          }
          
          // 如果数组是源数组（包括 sink 数组），或者索引/参数是复杂表达式，或者参数是污点源，检测为可疑
          // 改进：如果数组是 $GLOBALS 或 $_SESSION，且用于函数调用，也应该检测
          // 改进：如果底层变量在 sink_var_table 中，且参数是污点源或复杂表达式，应该检测
          if (is_source_array || is_sink_array || is_globals_or_session || 
              (has_complex_index && has_complex_args) || 
              (has_complex_index && current->kind == ZEND_AST_CALL) ||
              (is_sink_array && (has_tainted_args || has_complex_args)) ||
              (has_tainted_args && has_complex_args)) {
            printf("检测到可疑的数组访问函数调用: 数组=%s, 复杂索引=%d, 复杂参数=%d, 污点参数=%d, is_globals_or_session=%d, is_sink_array=%d\n", 
                   base_var_name ? ZSTR_VAL(base_var_name) : 
                   (dim_base && dim_base->kind == ZEND_AST_VAR && dim_base->child[0] && 
                    dim_base->child[0]->kind == ZEND_AST_ZVAL ? 
                    Z_STRVAL_P(zend_ast_get_zval(dim_base->child[0])) : "unknown"),
                   has_complex_index, has_complex_args, has_tainted_args, is_globals_or_session, is_sink_array);
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          }
        } else if (name_node->kind == ZEND_AST_CALL) { // file_get_contents(...)(...)
          // 函数名本身是一个函数调用，这是函数调用链模式
          // 例如：file_get_contents("php".$q)($_GET[2])
          zend_ast *inner_call = name_node;
          zend_ast *inner_name_node = inner_call->child[0];
          
          bool is_func_source_call = false;
          bool has_tainted_args = false;
          
          // 检查内层函数调用是否是 func_source_table 中的函数
          if (inner_name_node && inner_name_node->kind == ZEND_AST_ZVAL) {
            zval *inner_zv = zend_ast_get_zval(inner_name_node);
            if (inner_zv && Z_TYPE_P(inner_zv) == IS_STRING) {
              zend_string *inner_func_name = zend_ast_get_str(inner_name_node);
              if (zend_hash_exists(&func_source_table, inner_func_name)) {
                is_func_source_call = true;
                printf("DEBUG: 检测到函数调用链，内层函数 %s 在 func_source_table 中\n", Z_STRVAL_P(inner_zv));
              }
            }
          }
          
          // 检查外层函数调用的参数是否是污点源
          if (current->tainted == 1) {
            has_tainted_args = true;
            printf("DEBUG: 函数调用链的外层调用节点本身被标记为污点\n");
          } else {
            // 检查参数列表
            zend_ast **children = ast_get_children(current, &count);
            if (children && count > 1) {
              zend_ast *arg_list = children[1];
              if (arg_list && arg_list->kind == ZEND_AST_ARG_LIST) {
                zend_ast_list *args = zend_ast_get_list(arg_list);
                if (args && args->children > 0) {
                  for (uint32_t i = 0; i < args->children; i++) {
                    zend_ast *arg = args->child[i];
                    if (arg) {
                      // 检查参数是否被标记为污点
                      if (arg->tainted == 1) {
                        has_tainted_args = true;
                        printf("DEBUG: 检测到函数调用链的外层调用参数 %u 是污点\n", i);
                        break;
                      }
                      // 检查参数是否是超全局变量访问
                      if (arg->kind == ZEND_AST_DIM) {
                        zend_ast *arg_dim_base = arg->child[0];
                        if (arg_dim_base && arg_dim_base->kind == ZEND_AST_VAR) {
                          zend_ast *arg_var_name_node = arg_dim_base->child[0];
                          if (arg_var_name_node && arg_var_name_node->kind == ZEND_AST_ZVAL) {
                            zval *arg_zv = zend_ast_get_zval(arg_var_name_node);
                            if (arg_zv && Z_TYPE_P(arg_zv) == IS_STRING) {
                              const char *arg_var_name = Z_STRVAL_P(arg_zv);
                              if (strlen(arg_var_name) > 0 && arg_var_name[0] == '_' &&
                                  (strcmp(arg_var_name, "_POST") == 0 || 
                                   strcmp(arg_var_name, "_GET") == 0 ||
                                   strcmp(arg_var_name, "_REQUEST") == 0 ||
                                   strcmp(arg_var_name, "_SERVER") == 0 ||
                                   strcmp(arg_var_name, "_COOKIE") == 0 ||
                                   strcmp(arg_var_name, "_FILES") == 0)) {
                                has_tainted_args = true;
                                printf("DEBUG: 检测到函数调用链的外层调用参数是超全局变量访问: $%s[...]\n", arg_var_name);
                                break;
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          
          // 如果内层函数在 func_source_table 中，且外层调用的参数是污点源，应该检测
          // 或者即使参数不是污点，函数调用链模式本身就很可疑（因为通常用于混淆）
          if (is_func_source_call && (has_tainted_args || current->tainted == 1)) {
            printf("检测到可疑的函数调用链: 内层函数在 func_source_table 中，外层调用参数是污点源\n");
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          } else if (is_func_source_call) {
            // 即使参数不是污点，函数调用链模式本身也很可疑
            printf("检测到可疑的函数调用链: 内层函数在 func_source_table 中（函数调用链模式通常用于混淆）\n");
            if (!local)
              webshell = 1;
            else
              local_webshell = 1;
          }
        }
      }

    }
      zend_ast **ast_child = ast_get_children(current,&count);
      
      // 调试：输出当前节点的子节点信息
      if (current->kind == ZEND_AST_CALL || current->kind == ZEND_AST_ASSIGN || current->kind == ZEND_AST_STMT_LIST) {
        printf("DEBUG: webshell_check 处理节点 kind=%d，子节点数=%u\n", current->kind, count);
      }

      for (int i = 0; i < count; i++) { // 假设最多10个子节点
          int reverse_i = count - i - 1;
          if (ast_child[reverse_i] != NULL) {
              if (ast_child[reverse_i]->kind != ZEND_AST_FUNC_DECL)
                push(stack, ast_child[reverse_i]); // 将非空子节点加入栈
          }
      }
  }
  printf("DEBUG: webshell_check 总共处理了 %d 个节点\n", node_count);
  free(stack->data); // 释放栈内存
  free(stack);

}

//节点生成函数
zend_ast_zval* my_create_zval_ast(zval *zv, zend_ast *father) {
    zend_ast_zval *node = (zend_ast_zval *)emalloc(sizeof(zend_ast_zval));
    node->kind = ZEND_AST_ZVAL;
    node->attr = 0;
    ZVAL_COPY(&node->val, zv);
    node->tainted = 0;
    node->father = father;
    return node;
}

zend_ast_zval* my_create_zval_ast_arena(zval *zv, zend_ast *father, zend_arena **ast_arena) {
    zend_ast_zval *node = (zend_ast_zval *)zend_arena_alloc(ast_arena, sizeof(zend_ast_zval));
    node->kind = ZEND_AST_ZVAL;
    node->attr = 0;
    ZVAL_COPY(&node->val, zv);
    node->tainted = 0;
    node->father = father;
    return node;
}

zend_ast_list* my_create_ast_list(uint32_t children_count, zend_ast_kind kind) {
    size_t size = sizeof(zend_ast_list) + sizeof(zend_ast *) * (children_count -1);
    zend_ast_list *list = (zend_ast_list *)emalloc(size);
    
    // 初始化所有字段
    memset(list, 0, size);  // 先清零整个结构
    
    list->kind = kind;
    list->attr = 0;
    list->children = children_count;
    ((zend_ast*)list)->father = NULL;  // 初始化 father 字段
    ((zend_ast*)list)->tainted = 0;    // 初始化 tainted 字段
    
    for(uint32_t i = 0; i < children_count; i++) {
       list->child[i] = NULL;
    }
    return list;
}

zend_ast_list* my_create_ast_list_arena(uint32_t children_count, zend_ast_kind kind, zend_arena **ast_arena) {
    size_t size = sizeof(zend_ast_list) + sizeof(zend_ast *) * (children_count -1);
    zend_ast_list *list = (zend_ast_list *)zend_arena_alloc(ast_arena, size);
    
    // 初始化所有字段
    memset(list, 0, size);  // 先清零整个结构
    
    list->kind = kind;
    list->attr = 0;
    list->children = children_count;
    list->lineno = 0;  // 明确初始化 lineno
    ((zend_ast*)list)->father = NULL;  // 初始化 father 字段
    ((zend_ast*)list)->tainted = 0;    // 初始化 tainted 字段
    
    for(uint32_t i = 0; i < children_count; i++) {
       list->child[i] = NULL;
    }
    return list;
}

zend_ast *my_zend_ast_create(zend_ast_kind kind, zend_ast *child0, zend_ast *child1, zend_ast *father) {
    zend_ast *node = (zend_ast *)emalloc(sizeof(zend_ast));
    node->kind = kind;
    node->attr = 0;
    node->child[0] = child0;
    node->child[1] = child1;

    return node;
}

zend_ast *my_ast_create_ex(zend_ast_kind kind, uint32_t children, ...) {
    size_t size = sizeof(zend_ast) + (children - 1) * sizeof(zend_ast *);
    zend_ast *node = emalloc(size);

    node->kind = kind;
    node->attr = 0;
    node->lineno = 0;
    node->tainted = 0;
    node->father = NULL;

    va_list args;
    va_start(args, children);
    for (uint32_t i = 0; i < children; ++i) {
        node->child[i] = va_arg(args, zend_ast *);
    }
    va_end(args);

    return node;
}

zend_ast *my_ast_create_ex_arena(zend_ast_kind kind, uint32_t children, zend_arena **ast_arena, ...) {
    size_t size = sizeof(zend_ast) + (children - 1) * sizeof(zend_ast *);
    zend_ast *node = zend_arena_alloc(ast_arena, size);
    
    // 初始化所有字段
    memset(node, 0, size);

    node->kind = kind;
    node->attr = 0;
    node->lineno = 0;
    node->tainted = 0;
    node->father = NULL;

    va_list args;
    va_start(args, ast_arena);
    for (uint32_t i = 0; i < children; ++i) {
        node->child[i] = va_arg(args, zend_ast *);
    }
    va_end(args);
    
    // 确保未使用的子节点为 NULL
    for (uint32_t i = children; i < 10; ++i) {
        if (i < (size - sizeof(zend_ast)) / sizeof(zend_ast *)) {
            node->child[i] = NULL;
        }
    }

    return node;
}
zend_ast *create_var_ast(const char *var_name) {
    if (!var_name) {
        return NULL;
    }
    zval *zv = (zval *)emalloc(sizeof(zval));
    ZVAL_STR(zv, zend_string_init(var_name, strlen(var_name), 0));
    zend_ast *zval_ast = (zend_ast *)my_create_zval_ast(zv, NULL);

    zend_ast *var_ast = (zend_ast *)emalloc(sizeof(zend_ast));
    var_ast->kind = ZEND_AST_VAR;
    var_ast->attr = 0;
    var_ast->lineno = 0;
    var_ast->child[0] = zval_ast;

    return var_ast;
}

zend_ast *create_var_ast_arena(const char *var_name, zend_arena **ast_arena) {
    if (!var_name) {
        return NULL;
    }
    zval *zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(zv, zend_string_init(var_name, strlen(var_name), 0));
    zend_ast *zval_ast = (zend_ast *)my_create_zval_ast_arena(zv, NULL, ast_arena);

    zend_ast *var_ast = (zend_ast *)zend_arena_alloc(ast_arena, sizeof(zend_ast));
    var_ast->kind = ZEND_AST_VAR;
    var_ast->attr = 0;
    var_ast->lineno = 0;
    var_ast->tainted = 0;
    var_ast->father = NULL;
    var_ast->child[0] = zval_ast;
    var_ast->child[1] = NULL;

    return var_ast;
}

zend_ast *create_string_ast(const char *str) {
    zval *zv = (zval *)emalloc(sizeof(zval));
    ZVAL_STR(zv, zend_string_init(str, strlen(str), 0));
    return (zend_ast *)my_create_zval_ast(zv, NULL);  // ZEND_AST_ZVAL
}

// 替换原有 或'||'的定义
#ifndef T_BOOLEAN_OR
#define T_BOOLEAN_OR 285
#endif
#ifndef ZEND_BINARY_OP_OR
#define ZEND_BINARY_OP_OR T_BOOLEAN_OR
#endif

//cause seg
zend_ast *create_binary_op_ast(uint32_t op_type, zend_ast *left, zend_ast *right, zend_arena **ast_arena) {
    zend_ast *node = my_ast_create_ex_arena(ZEND_AST_BINARY_OP, 2, ast_arena, left, right);
    
    // 直接使用操作符类型，不进行任何转换
    node->attr = op_type;
    
    return node;
}

// 替代 create_unary_op_ast
zend_ast *create_unary_op_ast(zend_ast_attr op_type, zend_ast *expr, zend_arena **ast_arena) {
    zend_ast *node = my_ast_create_ex_arena(ZEND_AST_UNARY_OP, 1, ast_arena, expr);
    node->attr = op_type;
    return node;
}

const char* get_var_name(zend_ast *var_ast) {
    if (!var_ast || var_ast->kind != ZEND_AST_VAR) {
        return NULL;
    }
    zend_ast *name_ast = var_ast->child[0];
    if (!name_ast) {
        return NULL;
    }
    if (name_ast->kind == ZEND_AST_ZVAL) {
        zval *zv = zend_ast_get_zval(name_ast);
        if (Z_TYPE_P(zv) == IS_STRING) {
            return Z_STRVAL_P(zv);
        }
    }
    return NULL;
}

// 递归深拷贝AST节点
zend_ast* deep_copy_ast(zend_ast *ast, zend_arena **ast_arena) {
    if (!ast) return NULL;
    
    if (ast_kind_is_decl(ast->kind)) {
        // 处理声明类型节点
        zend_ast_decl *decl = (zend_ast_decl*)ast;
        zend_ast_decl *new_decl = (zend_ast_decl*)zend_arena_alloc(ast_arena, sizeof(zend_ast_decl));
        
        memcpy(new_decl, decl, sizeof(zend_ast_decl));
        for (uint32_t i = 0; i < 5; i++) {
            new_decl->child[i] = deep_copy_ast(decl->child[i], ast_arena);
            if (new_decl->child[i]) 
               new_decl->child[i]->father = (zend_ast*)new_decl;
        }
        
        if (decl->name) 
           new_decl->name = zend_string_copy(decl->name);
        if (decl->doc_comment) 
           new_decl->doc_comment = zend_string_copy(decl->doc_comment);
        
        return (zend_ast*)new_decl;
    } else if (zend_ast_is_list(ast)) {
        // 处理列表类型节点
        zend_ast_list *list = zend_ast_get_list(ast);
        zend_ast_list *new_list = my_create_ast_list(list->children, ast->kind);
        
        new_list->attr = list->attr;
        new_list->lineno = list->lineno;
        new_list->tainted = list->tainted;
        new_list->father = NULL;
        
        for (uint32_t i = 0; i < list->children; i++) {
            new_list->child[i] = deep_copy_ast(list->child[i], ast_arena);
            if (new_list->child[i]) 
               new_list->child[i]->father = (zend_ast*)new_list;
        }
        
        return (zend_ast*)new_list;
    } else if (ast->kind == ZEND_AST_ZVAL) {
        // 处理ZVAL类型节点
        zend_ast_zval *zval_ast = (zend_ast_zval*)ast;
        zend_ast_zval *new_zval_ast = (zend_ast_zval*)zend_arena_alloc(ast_arena, sizeof(zend_ast_zval));
        
        new_zval_ast->kind = ZEND_AST_ZVAL;
        new_zval_ast->attr = zval_ast->attr;
        
        zval *zv = zend_ast_get_zval(ast);
        zval new_zv;
        ZVAL_COPY(&new_zv, zv);
        ZVAL_COPY_VALUE(&new_zval_ast->val, &new_zv);
        
        if (ast->father) {
            ((zend_ast*)new_zval_ast)->father = ast->father;
        }
        
        return (zend_ast*)new_zval_ast;
    } else {
        // 处理普通节点
        uint32_t children = zend_ast_get_num_children(ast);
        size_t size = sizeof(zend_ast) + (children > 1 ? (children - 1) * sizeof(zend_ast*) : 0);
        zend_ast *new_ast = zend_arena_alloc(ast_arena, size);
        
        new_ast->kind = ast->kind;
        new_ast->attr = ast->attr;
        new_ast->lineno = ast->lineno;
        new_ast->tainted = ast->tainted;
        new_ast->father = NULL;
        
        for (uint32_t i = 0; i < children; i++) {
            new_ast->child[i] = deep_copy_ast(ast->child[i], ast_arena);
            if (new_ast->child[i]) 
               new_ast->child[i]->father = new_ast;
        }
        
        return new_ast;
    }
}

//深拷贝整个数组节点，用一个新的变量节点来=整个数组节点，通过对变量节点进行判断
zend_ast* deep_copy_dim_to_var(zend_ast *dim_ast, zend_arena **ast_arena, const char *new_var_name) {
    zend_ast *var_ast = create_var_ast_arena(new_var_name, ast_arena);
    zend_ast *dim_copy = deep_copy_ast(dim_ast, ast_arena);

    zend_ast *assign_ast = my_ast_create_ex_arena(ZEND_AST_ASSIGN, 2, ast_arena, var_ast, dim_copy);

    return assign_ast; 
}

static zend_ast* build_in_array_check(zend_ast *var_ast, zend_arena **ast_arena) {
    /* 1) 构造 ["eval","assert",... ] 的数组常量 */
    const char *dangerous_func_names[] = {
        "eval", "assert", "exec", "shell_exec", "system", "preg_replace",
        "file_put_contents", "fwrite", "fputs", "call_user_func_array",
        "array_map", "copy", "call_user_func", "array_filter", "array_walk",
        "array_walk_recursive", "register_tick_function", "eval_r",
        "create_function", "uasort", "array_udiff_assoc",
        "forward_static_call_array", "uksort", "array_reduce",
        "register_shutdown_function", "filter_var", "filter_var_array",
        "preg_replace_callback", "mb_ereg_replace_callback", "popen"
    };
    size_t num_funcs = sizeof(dangerous_func_names) / sizeof(dangerous_func_names[0]);

    /* ZEND_AST_ARRAY: children = num_funcs */
    zend_ast_list *arr_list = my_create_ast_list_arena((uint32_t)num_funcs, ZEND_AST_ARRAY, ast_arena);
    for (uint32_t i = 0; i < (uint32_t)num_funcs; ++i) {
        zval *name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
        ZVAL_STR(name_zv, zend_string_init(dangerous_func_names[i], strlen(dangerous_func_names[i]), 0));
        zend_ast *val_node = (zend_ast *)my_create_zval_ast_arena(name_zv, NULL, ast_arena); /* ZEND_AST_ZVAL */

        /* ZEND_AST_ARRAY_ELEM(value, key=NULL) */
        zend_ast *elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, val_node, NULL);
        arr_list->child[i] = elem;
        elem->father = (zend_ast*)arr_list;
    }

    /* 2) 构造 in_array($var, ["..."], true) 调用 */
    zval *in_array_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(in_array_name_zv, zend_string_init("in_array", sizeof("in_array")-1, 0));
    zend_ast *in_array_name_ast = (zend_ast *)my_create_zval_ast_arena(in_array_name_zv, NULL, ast_arena); /* name 节点 */

    /* 第3个参数 true */
    zval *true_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_TRUE(true_zv);
    zend_ast *true_ast = (zend_ast *)my_create_zval_ast_arena(true_zv, NULL, ast_arena);

    /* 参数列表：($var, array_const, true) */
    zend_ast_list *in_array_args = my_create_ast_list_arena(3, ZEND_AST_ARG_LIST, ast_arena);
    in_array_args->child[0] = var_ast;                 /* 直接使用传入的变量 AST */
    in_array_args->child[1] = (zend_ast *)arr_list;    /* 数组常量 */
    in_array_args->child[2] = true_ast;

    /* in_array 调用节点 */
    zend_ast *in_array_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        in_array_name_ast, (zend_ast*)in_array_args);
    return in_array_call; /* 作为 if 的条件 */
}

/* 建议1：构造 __yz_runtime_probe 调用 AST */
static zend_ast* build_probe_call_for_call_ast(
    zend_ast *call_ast,
    zend_arena **ast_arena,
    const char *type_str,
    zend_ast *callee_ast,
    zend_ast *first_arg_ast
) {
    if (!call_ast || !ast_arena || !type_str) return NULL;
    
    /* 1) 函数名：__yz_runtime_probe */
    zval *probe_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(probe_name_zv, zend_string_init("__yz_runtime_probe", strlen("__yz_runtime_probe"), 0));
    zend_ast *probe_name_ast = (zend_ast *)my_create_zval_ast_arena(probe_name_zv, NULL, ast_arena);
    
    /* 2) 参数列表：type, __FILE__, __LINE__, __FUNCTION__, callee, [args...] */
    /* 参数1：type 字符串 */
    zval *type_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(type_zv, zend_string_init(type_str, strlen(type_str), 0));
    zend_ast *type_ast = (zend_ast *)my_create_zval_ast_arena(type_zv, NULL, ast_arena);
    
    /* 参数2：__FILE__ */
    zval *file_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(file_name_zv, zend_string_init("__FILE__", 8, 0));
    zend_ast *file_name_ast = (zend_ast *)my_create_zval_ast_arena(file_name_zv, NULL, ast_arena);
    
    /* 参数3：__LINE__ */
    zval *line_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(line_name_zv, zend_string_init("__LINE__", 8, 0));
    zend_ast *line_name_ast = (zend_ast *)my_create_zval_ast_arena(line_name_zv, NULL, ast_arena);
    
    /* 参数4：__FUNCTION__ */
    zval *func_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(func_name_zv, zend_string_init("__FUNCTION__", 12, 0));
    zend_ast *func_name_ast = (zend_ast *)my_create_zval_ast_arena(func_name_zv, NULL, ast_arena);
    
    /* 计算参数数量 */
    uint32_t arg_count = 4;  // type, __FILE__, __LINE__, __FUNCTION__
    if (callee_ast) arg_count++;
    if (first_arg_ast) arg_count++;
    
    zend_ast_list *probe_args = my_create_ast_list_arena(arg_count, ZEND_AST_ARG_LIST, ast_arena);
    probe_args->child[0] = type_ast;
    probe_args->child[1] = file_name_ast;
    probe_args->child[2] = line_name_ast;
    probe_args->child[3] = func_name_ast;
    
    uint32_t idx = 4;
    if (callee_ast) {
        probe_args->child[idx++] = callee_ast;
    }
    if (first_arg_ast) {
        probe_args->child[idx++] = first_arg_ast;
    }
    
    /* 构造 __yz_runtime_probe(...) 调用 */
    zend_ast *probe_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        probe_name_ast, (zend_ast*)probe_args);
    
    return probe_call;
}

/* 用于构造：file_put_contents("/tmp/yz_dyn_cg.jsonl", json_encode([...]), FILE_APPEND); */
/* 生成 JSON 格式的日志：{"type":"dyn_call","file":__FILE__,"line":__LINE__,"caller":__FUNCTION__,"callee":$var} */
/* 注意：var_name 参数用于在日志中记录变量名 */
static zend_ast* build_call_var_log_stmt(zend_ast *var_ast, const char *var_name, zend_arena **ast_arena) {
    /* 函数名：file_put_contents */
    zval *fput_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(fput_name_zv, zend_string_init("file_put_contents", sizeof("file_put_contents")-1, 0));
    zend_ast *fput_name_ast = (zend_ast *)my_create_zval_ast_arena(fput_name_zv, NULL, ast_arena);

    /* 参数1：日志路径 - 改为调用图日志 */
    zval *path_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(path_zv, zend_string_init("/tmp/yz_dyn_cg.jsonl", sizeof("/tmp/yz_dyn_cg.jsonl")-1, 0));
    zend_ast *path_ast = (zend_ast *)my_create_zval_ast_arena(path_zv, NULL, ast_arena);

    /* 参数2：构建 JSON 字符串 - 调用图日志格式
     * 生成代码：json_encode(["type" => "dyn_call", "file" => __FILE__, "line" => __LINE__, 
     *                        "caller" => __FUNCTION__, "callee" => $var]) . "\n"
     */
    
    /* 构建数组：["type" => "dyn_call", "file" => __FILE__, "line" => __LINE__, 
     *            "caller" => __FUNCTION__, "callee" => is_string($var) ? $var : null] */
    /* "type" => "dyn_call" */
    zval *type_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(type_key_zv, zend_string_init("type", 4, 0));
    zend_ast *type_key_ast = (zend_ast *)my_create_zval_ast_arena(type_key_zv, NULL, ast_arena);
    
    zval *type_val_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(type_val_zv, zend_string_init("dyn_call", 8, 0));
    zend_ast *type_val_ast = (zend_ast *)my_create_zval_ast_arena(type_val_zv, NULL, ast_arena);
    
    zend_ast *type_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, type_val_ast, type_key_ast);
    
    /* "file" => __FILE__ */
    zval *file_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(file_key_zv, zend_string_init("file", 4, 0));
    zend_ast *file_key_ast = (zend_ast *)my_create_zval_ast_arena(file_key_zv, NULL, ast_arena);
    
    zval *file_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(file_name_zv, zend_string_init("__FILE__", 8, 0));
    zend_ast *file_name_ast = (zend_ast *)my_create_zval_ast_arena(file_name_zv, NULL, ast_arena);
    /* 注意：这里需要构建常量 __FILE__，但为了简化，我们直接使用字符串 */
    /* 实际上在运行时 __FILE__ 会被解析为实际文件名 */
    
    zend_ast *file_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, file_name_ast, file_key_ast);
    
    /* "line" => __LINE__ */
    zval *line_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(line_key_zv, zend_string_init("line", 4, 0));
    zend_ast *line_key_ast = (zend_ast *)my_create_zval_ast_arena(line_key_zv, NULL, ast_arena);
    
    zval *line_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(line_name_zv, zend_string_init("__LINE__", 8, 0));
    zend_ast *line_name_ast = (zend_ast *)my_create_zval_ast_arena(line_name_zv, NULL, ast_arena);
    
    zend_ast *line_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, line_name_ast, line_key_ast);
    
    /* 构建 "var" => "var_name" (变量名字符串) */
    zval *var_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(var_key_zv, zend_string_init("var", 3, 0));
    zend_ast *var_key_ast = (zend_ast *)my_create_zval_ast_arena(var_key_zv, NULL, ast_arena);
    
    zval *var_val_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    if (var_name) {
        ZVAL_STR(var_val_zv, zend_string_init(var_name, strlen(var_name), 0));
    } else {
        ZVAL_STR(var_val_zv, zend_string_init("", 0, 0));
    }
    zend_ast *var_val_ast = (zend_ast *)my_create_zval_ast_arena(var_val_zv, NULL, ast_arena);
    
    zend_ast *var_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, var_val_ast, var_key_ast);
    
    /* 构建 "caller" => current_function_name (调用者函数名) */
    zval *caller_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(caller_key_zv, zend_string_init("caller", 6, 0));
    zend_ast *caller_key_ast = (zend_ast *)my_create_zval_ast_arena(caller_key_zv, NULL, ast_arena);
    
    zval *caller_val_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    if (current_function_name) {
        ZVAL_STR(caller_val_zv, zend_string_copy(current_function_name));
    } else {
        ZVAL_STR(caller_val_zv, zend_string_init("__main__", 8, 0));
    }
    zend_ast *caller_val_ast = (zend_ast *)my_create_zval_ast_arena(caller_val_zv, NULL, ast_arena);
    
    zend_ast *caller_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, caller_val_ast, caller_key_ast);
    
    /* "callee" => is_string($var) ? $var : null */
    /* is_string($var) */
    zval *is_string_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(is_string_name_zv, zend_string_init("is_string", 9, 0));
    zend_ast *is_string_name_ast = (zend_ast *)my_create_zval_ast_arena(is_string_name_zv, NULL, ast_arena);
    
    zend_ast_list *is_string_args = my_create_ast_list_arena(1, ZEND_AST_ARG_LIST, ast_arena);
    is_string_args->child[0] = var_ast;
    
    zend_ast *is_string_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        is_string_name_ast, (zend_ast*)is_string_args);
    
    /* null */
    zval *null_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_NULL(null_zv);
    zend_ast *null_ast = (zend_ast *)my_create_zval_ast_arena(null_zv, NULL, ast_arena);
    
    /* is_string($var) ? $var : null */
    zend_ast *callee_val_ast = my_ast_create_ex_arena(ZEND_AST_CONDITIONAL, 3, ast_arena,
        is_string_call, var_ast, null_ast);
    
    zval *callee_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(callee_key_zv, zend_string_init("callee", 6, 0));
    zend_ast *callee_key_ast = (zend_ast *)my_create_zval_ast_arena(callee_key_zv, NULL, ast_arena);
    
    zend_ast *callee_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, callee_val_ast, callee_key_ast);
    
    /* 构建数组 [type_elem, file_elem, line_elem, caller_elem, callee_elem] */
    zend_ast_list *json_array = my_create_ast_list_arena(5, ZEND_AST_ARRAY, ast_arena);
    json_array->child[0] = type_elem;
    json_array->child[1] = file_elem;
    json_array->child[2] = line_elem;
    json_array->child[3] = caller_elem;
    json_array->child[4] = callee_elem;
    
    /* json_encode(...) */
    zval *json_encode_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(json_encode_name_zv, zend_string_init("json_encode", 10, 0));
    zend_ast *json_encode_name_ast = (zend_ast *)my_create_zval_ast_arena(json_encode_name_zv, NULL, ast_arena);
    
    zend_ast_list *json_encode_args = my_create_ast_list_arena(1, ZEND_AST_ARG_LIST, ast_arena);
    json_encode_args->child[0] = (zend_ast*)json_array;
    
    zend_ast *json_encode_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        json_encode_name_ast, (zend_ast*)json_encode_args);
    
    /* json_encode(...) . "\n" */
    zval *nl_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(nl_zv, zend_string_init("\n", 1, 0));
    zend_ast *nl_ast = (zend_ast *)my_create_zval_ast_arena(nl_zv, NULL, ast_arena);
    zend_ast *msg_ast = create_binary_op_ast(ZEND_CONCAT, json_encode_call, nl_ast, ast_arena);

    /* 参数3：flags = FILE_APPEND = 8 */
    zval *flags_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_LONG(flags_zv, 8);  // FILE_APPEND
    zend_ast *flags_ast = (zend_ast *)my_create_zval_ast_arena(flags_zv, NULL, ast_arena);

    /* 实参列表 */
    zend_ast_list *args = my_create_ast_list_arena(3, ZEND_AST_ARG_LIST, ast_arena);
    args->child[0] = path_ast;
    args->child[1] = msg_ast;
    args->child[2] = flags_ast;

    /* 调用节点 */
    zend_ast *call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        fput_name_ast, (zend_ast*)args);
    return call;
}

/* 用于构造：file_put_contents("/tmp/yz_assert_log.jsonl", "[BLOCK] fn=" . $var . "\n", 10); */
/* 保留旧版本以兼容，但建议使用 build_call_var_log_stmt */
static zend_ast* build_file_put_contents_stmt(zend_ast *var_ast, zend_arena **ast_arena) {
    /* 函数名 */
    zval *fput_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(fput_name_zv, zend_string_init("file_put_contents", sizeof("file_put_contents")-1, 0));
    zend_ast *fput_name_ast = (zend_ast *)my_create_zval_ast_arena(fput_name_zv, NULL, ast_arena);

    /* 参数1：日志路径 */
    zval *path_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(path_zv, zend_string_init("/tmp/yz_assert_log.jsonl", sizeof("/tmp/yz_assert_log.jsonl")-1, 0));
    zend_ast *path_ast = (zend_ast *)my_create_zval_ast_arena(path_zv, NULL, ast_arena);

    /* 参数2：拼接消息 "[BLOCK] fn=" . $var . "\n" */
    zval *prefix_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(prefix_zv, zend_string_init("[BLOCK] fn=", sizeof("[BLOCK] fn=")-1, 0));
    zend_ast *prefix_ast = (zend_ast *)my_create_zval_ast_arena(prefix_zv, NULL, ast_arena);

    /* prefix . var */
    zend_ast *prefix_concat_var = create_binary_op_ast(ZEND_CONCAT, prefix_ast, var_ast, ast_arena);

    /* (prefix . var) . "\n" */
    zval *nl_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(nl_zv, zend_string_init("\n", 1, 0));
    zend_ast *nl_ast = (zend_ast *)my_create_zval_ast_arena(nl_zv, NULL, ast_arena);
    zend_ast *msg_ast = create_binary_op_ast(ZEND_CONCAT, prefix_concat_var, nl_ast, ast_arena);

    /* 参数3：flags = FILE_APPEND|LOCK_EX = 8|2 = 10 */
    zval *flags_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_LONG(flags_zv, 10);
    zend_ast *flags_ast = (zend_ast *)my_create_zval_ast_arena(flags_zv, NULL, ast_arena);

    /* 实参列表 */
    zend_ast_list *args = my_create_ast_list_arena(3, ZEND_AST_ARG_LIST, ast_arena);
    args->child[0] = path_ast;
    args->child[1] = msg_ast;
    args->child[2] = flags_ast;

    /* 调用节点 */
    zend_ast *call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        fput_name_ast, (zend_ast*)args);
    return call;
}

/* 用于构造：file_put_contents("/tmp/yz_dyn_cg.jsonl", json_encode([...]), FILE_APPEND); */
/* 生成 JSON 格式的日志：{"type":"eval","file":__FILE__,"line":__LINE__} */
static zend_ast* build_eval_log_stmt(zend_ast *eval_node, zend_arena **ast_arena) {
    /* 函数名：file_put_contents */
    zval *fput_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(fput_name_zv, zend_string_init("file_put_contents", sizeof("file_put_contents")-1, 0));
    zend_ast *fput_name_ast = (zend_ast *)my_create_zval_ast_arena(fput_name_zv, NULL, ast_arena);

    /* 参数1：日志路径 - 改为调用图日志 */
    zval *path_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(path_zv, zend_string_init("/tmp/yz_dyn_cg.jsonl", sizeof("/tmp/yz_dyn_cg.jsonl")-1, 0));
    zend_ast *path_ast = (zend_ast *)my_create_zval_ast_arena(path_zv, NULL, ast_arena);

    /* 参数2：构建 JSON 字符串 json_encode(["type" => "EVAL", "line" => __LINE__]) . "\n" */
    
    /* 构建数组：["type" => "EVAL", "line" => lineno] */
    /* "type" => "EVAL" */
    zval *type_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(type_key_zv, zend_string_init("type", 4, 0));
    zend_ast *type_key_ast = (zend_ast *)my_create_zval_ast_arena(type_key_zv, NULL, ast_arena);
    
    zval *type_val_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(type_val_zv, zend_string_init("eval", 4, 0));
    zend_ast *type_val_ast = (zend_ast *)my_create_zval_ast_arena(type_val_zv, NULL, ast_arena);
    
    zend_ast *type_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, type_val_ast, type_key_ast);
    
    /* "file" => __FILE__ */
    zval *file_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(file_key_zv, zend_string_init("file", 4, 0));
    zend_ast *file_key_ast = (zend_ast *)my_create_zval_ast_arena(file_key_zv, NULL, ast_arena);
    
    zval *file_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(file_name_zv, zend_string_init("__FILE__", 8, 0));
    zend_ast *file_name_ast = (zend_ast *)my_create_zval_ast_arena(file_name_zv, NULL, ast_arena);
    
    zend_ast *file_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, file_name_ast, file_key_ast);
    
    /* "line" => __LINE__ */
    zval *line_key_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(line_key_zv, zend_string_init("line", 4, 0));
    zend_ast *line_key_ast = (zend_ast *)my_create_zval_ast_arena(line_key_zv, NULL, ast_arena);
    
    zval *line_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(line_name_zv, zend_string_init("__LINE__", 8, 0));
    zend_ast *line_name_ast = (zend_ast *)my_create_zval_ast_arena(line_name_zv, NULL, ast_arena);
    
    zend_ast *line_elem = my_ast_create_ex_arena(ZEND_AST_ARRAY_ELEM, 2, ast_arena, line_name_ast, line_key_ast);
    
    /* 构建数组 [type_elem, file_elem, line_elem] */
    zend_ast_list *json_array = my_create_ast_list_arena(3, ZEND_AST_ARRAY, ast_arena);
    json_array->child[0] = type_elem;
    json_array->child[1] = file_elem;
    json_array->child[2] = line_elem;
    
    /* json_encode(...) */
    zval *json_encode_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(json_encode_name_zv, zend_string_init("json_encode", 10, 0));
    zend_ast *json_encode_name_ast = (zend_ast *)my_create_zval_ast_arena(json_encode_name_zv, NULL, ast_arena);
    
    zend_ast_list *json_encode_args = my_create_ast_list_arena(1, ZEND_AST_ARG_LIST, ast_arena);
    json_encode_args->child[0] = (zend_ast*)json_array;
    
    zend_ast *json_encode_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        json_encode_name_ast, (zend_ast*)json_encode_args);
    
    /* json_encode(...) . "\n" */
    zval *nl_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(nl_zv, zend_string_init("\n", 1, 0));
    zend_ast *nl_ast = (zend_ast *)my_create_zval_ast_arena(nl_zv, NULL, ast_arena);
    zend_ast *msg_ast = create_binary_op_ast(ZEND_CONCAT, json_encode_call, nl_ast, ast_arena);

    /* 参数3：flags = FILE_APPEND = 8 */
    zval *flags_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_LONG(flags_zv, 8);  // FILE_APPEND
    zend_ast *flags_ast = (zend_ast *)my_create_zval_ast_arena(flags_zv, NULL, ast_arena);

    /* 实参列表 */
    zend_ast_list *args = my_create_ast_list_arena(3, ZEND_AST_ARG_LIST, ast_arena);
    args->child[0] = path_ast;
    args->child[1] = msg_ast;
    args->child[2] = flags_ast;

    /* 调用节点 */
    zend_ast *call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        fput_name_ast, (zend_ast*)args);
    return call;
}

/* 构造：exit(1); 作为语句 */
static zend_ast* build_exit_stmt(zend_arena **ast_arena) {
    zval *one_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_LONG(one_zv, 1);
    zend_ast *one_ast = (zend_ast *)my_create_zval_ast_arena(one_zv, NULL, ast_arena);
    zend_ast *exit_ast = my_ast_create_ex_arena(ZEND_AST_EXIT, 1, ast_arena, one_ast);
    return exit_ast;
}

/* 建议1：用 assert(__yz_runtime_probe(...)) 替换原先的 if + file_put_contents */
zend_ast* insert_assert_before_at_index(zend_ast *stmt_list_ast, uint32_t index, zend_arena **ast_arena, char *var_name) {
    if (!stmt_list_ast || stmt_list_ast->kind != ZEND_AST_STMT_LIST) return stmt_list_ast;
    if (!var_name) return stmt_list_ast;

    /* 构造 $var 节点 */
    zend_ast *var_ast = create_var_ast_arena(var_name, ast_arena);
    if (!var_ast) {
        return stmt_list_ast;
    }

    /* 构造 __yz_runtime_probe("CALL_VAR", __FILE__, __LINE__, __FUNCTION__, $var) */
    zend_ast *probe_call = build_probe_call_for_call_ast(
        NULL,  // call_ast 不需要，因为我们只传参数
        ast_arena,
        "CALL_VAR",
        var_ast,  // callee_ast
        NULL      // first_arg_ast，对于 CALL_VAR 暂时不传参数
    );
    
    if (!probe_call) {
        return stmt_list_ast;
    }

    /* 构造 assert(__yz_runtime_probe(...)) */
    zval *assert_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
    ZVAL_STR(assert_name_zv, zend_string_init("assert", 6, 0));
    zend_ast *assert_name_ast = (zend_ast *)my_create_zval_ast_arena(assert_name_zv, NULL, ast_arena);
    
    zend_ast_list *assert_args = my_create_ast_list_arena(1, ZEND_AST_ARG_LIST, ast_arena);
    assert_args->child[0] = probe_call;
    
    zend_ast *assert_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
        assert_name_ast, (zend_ast*)assert_args);

    /* 把 assert 语句插入到 stmt_list_ast 的 index 位置 */
    zend_ast_list *list = zend_ast_get_list(stmt_list_ast);
    uint32_t old_n = list->children;
    if (index > old_n) index = old_n;

    zend_ast_list *new_list = my_create_ast_list_arena(old_n + 1, ZEND_AST_STMT_LIST, ast_arena);
    for (uint32_t i = 0; i < index; i++) {
        new_list->child[i] = list->child[i];
        if (new_list->child[i]) new_list->child[i]->father = (zend_ast*)new_list;
    }
    new_list->child[index] = assert_call;
    if (new_list->child[index]) new_list->child[index]->father = (zend_ast*)new_list;

    for (uint32_t i = index; i < old_n; i++) {
        new_list->child[i+1] = list->child[i];
        if (new_list->child[i+1]) new_list->child[i+1]->father = (zend_ast*)new_list;
    }

    // 设置 new_list 的 father 指针
    ((zend_ast*)new_list)->father = stmt_list_ast->father;

    return (zend_ast*)new_list;
}

static void replace_child_in_parent(zend_ast *parent, zend_ast *old_child, zend_ast *new_child) {
    if (!parent || !old_child || !new_child) return;
    if (old_child == new_child) return;  // 避免替换自身
    
    uint32_t count = 0;
    zend_ast **children = ast_get_children(parent, &count);
    if (!children) return;
    
    for (uint32_t i = 0; i < count; i++) {
        if (children[i] == old_child) {
            children[i] = new_child;
            if (new_child) {
                new_child->father = parent;
            }
            return;
        }
    }
}

//对数组节点检测插入赋值语句
static zend_ast* insert_stmt_before_at_index(zend_ast *stmt_list_ast, uint32_t index, zend_ast *stmt, zend_arena **ast_arena) {
    if (!stmt_list_ast || stmt_list_ast->kind != ZEND_AST_STMT_LIST) return stmt_list_ast;
    zend_ast_list *list = zend_ast_get_list(stmt_list_ast);
    uint32_t old_n = list->children;
    if (index > old_n) index = old_n;

    zend_ast_list *new_list = my_create_ast_list_arena(old_n + 1, ZEND_AST_STMT_LIST, ast_arena);

    for (uint32_t i = 0; i < index; i++) {
        new_list->child[i] = list->child[i];
        if (new_list->child[i]) new_list->child[i]->father = (zend_ast*)new_list;
    }
    new_list->child[index] = stmt;
    if (stmt) stmt->father = (zend_ast*)new_list;

    for (uint32_t i = index; i < old_n; i++) {
        new_list->child[i + 1] = list->child[i];
        if (new_list->child[i + 1]) new_list->child[i + 1]->father = (zend_ast*)new_list;
    }

    // 设置 new_list 的 father 指针
    ((zend_ast*)new_list)->father = stmt_list_ast->father;

    return (zend_ast*)new_list;
}

static zend_bool is_known_sink_function(zend_string *func_name) {
    if (!func_name) {
        return 0;
    }
    if (zend_hash_exists(&sink_table, func_name)) {
        return 1;
    }
    if (zend_hash_exists(&sink_func_table, func_name)) {
        return 1;
    }
    if (zend_hash_exists(&webshell_table, func_name)) {
        return 1;
    }
    return 0;
}

// 检查字符串是否是有效的十六进制字符串
static zend_bool is_hex_string(zend_string *str) {
    if (!str || ZSTR_LEN(str) == 0) {
        return 0;
    }
    const char *s = ZSTR_VAL(str);
    size_t len = ZSTR_LEN(str);
    // 十六进制字符串长度必须是偶数
    if (len % 2 != 0) {
        return 0;
    }
    // 检查每个字符是否是十六进制字符
    for (size_t i = 0; i < len; i++) {
        if (!((s[i] >= '0' && s[i] <= '9') || 
              (s[i] >= 'a' && s[i] <= 'f') || 
              (s[i] >= 'A' && s[i] <= 'F'))) {
            return 0;
        }
    }
    return 1;
}

// 将十六进制字符串解码为普通字符串
static zend_string* hex_decode_string(zend_string *hex_str) {
    if (!hex_str || !is_hex_string(hex_str)) {
        return NULL;
    }
    const char *hex = ZSTR_VAL(hex_str);
    size_t hex_len = ZSTR_LEN(hex_str);
    size_t decoded_len = hex_len / 2;
    zend_string *result = zend_string_alloc(decoded_len, 0);
    char *out = ZSTR_VAL(result);
    
    for (size_t i = 0; i < decoded_len; i++) {
        char c1 = hex[i * 2];
        char c2 = hex[i * 2 + 1];
        int val1 = (c1 >= '0' && c1 <= '9') ? (c1 - '0') : 
                   (c1 >= 'a' && c1 <= 'f') ? (c1 - 'a' + 10) : (c1 - 'A' + 10);
        int val2 = (c2 >= '0' && c2 <= '9') ? (c2 - '0') : 
                   (c2 >= 'a' && c2 <= 'f') ? (c2 - 'a' + 10) : (c2 - 'A' + 10);
        out[i] = (char)(val1 * 16 + val2);
    }
    ZSTR_VAL(result)[decoded_len] = '\0';
    ZSTR_LEN(result) = decoded_len;
    return result;
}

// 检查字符串是否包含危险函数名（不区分大小写）
static zend_bool contains_dangerous_function(zend_string *str) {
    if (!str) {
        return 0;
    }
    const char *s = ZSTR_VAL(str);
    size_t len = ZSTR_LEN(str);
    if (len == 0) {
        return 0;
    }
    
    // 危险函数名列表（不区分大小写）
    const char *dangerous_funcs[] = {
        "assert", "eval", "exec", "system", "shell_exec", "preg_replace",
        "file_put_contents", "fwrite", "fputs", "call_user_func",
        "call_user_func_array", "array_map", "create_function"
    };
    size_t num_funcs = sizeof(dangerous_funcs) / sizeof(dangerous_funcs[0]);
    
    // 转换为小写进行比较
    char *lower_str = (char *)malloc(len + 1);
    for (size_t i = 0; i < len; i++) {
        lower_str[i] = tolower((unsigned char)s[i]);
    }
    lower_str[len] = '\0';
    
    for (size_t i = 0; i < num_funcs; i++) {
        const char *func_name = dangerous_funcs[i];
        size_t func_len = strlen(func_name);
        if (strstr(lower_str, func_name) != NULL) {
            free(lower_str);
            return 1;
        }
    }
    
    free(lower_str);
    return 0;
}

static void add_sink_var_from_assignment(zend_ast *var_node, zend_string *func_name) {
    if (!var_node || var_node->kind != ZEND_AST_VAR || !func_name) {
        return;
    }
    zend_ast *name_node = var_node->child[0];
    if (!name_node || name_node->kind != ZEND_AST_ZVAL) {
        return;
    }
    zval *zv = zend_ast_get_zval(name_node);
    if (!zv || Z_TYPE_P(zv) != IS_STRING) {
        return;
    }
    zend_string *var_name = zend_ast_get_str(name_node);
    if (!var_name) {
        return;
    }
    if (!zend_hash_exists(&sink_var_table, var_name)) {
        zval sink_var_val;
        ZVAL_LONG(&sink_var_val, sink_var_count);
        sink_var_count++;
        zend_hash_add(&sink_var_table, var_name, &sink_var_val);
        printf("动态识别危险函数变量: $%s -> %s\n", var_name->val, ZSTR_VAL(func_name));
    }
}

// 评估数字表达式（如 65-1, 10+5 等）
static zend_long evaluate_numeric_expression(zend_ast *expr) {
    if (!expr) return 0;
    switch (expr->kind) {
        case ZEND_AST_ZVAL: {
            zval *zv = zend_ast_get_zval(expr);
            if (!zv) return 0;
            if (Z_TYPE_P(zv) == IS_LONG) {
                return Z_LVAL_P(zv);
            } else if (Z_TYPE_P(zv) == IS_DOUBLE) {
                return (zend_long)Z_DVAL_P(zv);
            } else if (Z_TYPE_P(zv) == IS_STRING) {
                // 尝试将字符串转换为数字
                zend_long lval;
                double dval;
                if (is_numeric_string(Z_STRVAL_P(zv), Z_STRLEN_P(zv), &lval, &dval, 0)) {
                    return lval;
                }
            }
            return 0;
        }
        case ZEND_AST_VAR: {
            // 从变量值表中查找变量值
            zend_ast *name_node = expr->child[0];
            if (!name_node || name_node->kind != ZEND_AST_ZVAL) {
                return 0;
            }
            zval *zv = zend_ast_get_zval(name_node);
            if (!zv || Z_TYPE_P(zv) != IS_STRING) {
                return 0;
            }
            zend_string *var_name = zend_ast_get_str(name_node);
            if (!var_name) {
                return 0;
            }
            zval *var_val = zend_hash_find(&var_value_table, var_name);
            if (var_val) {
                if (Z_TYPE_P(var_val) == IS_LONG) {
                    return Z_LVAL_P(var_val);
                } else if (Z_TYPE_P(var_val) == IS_DOUBLE) {
                    return (zend_long)Z_DVAL_P(var_val);
                } else if (Z_TYPE_P(var_val) == IS_STRING) {
                    zend_long lval;
                    double dval;
                    if (is_numeric_string(Z_STRVAL_P(var_val), Z_STRLEN_P(var_val), &lval, &dval, 0)) {
                        return lval;
                    }
                }
            }
            return 0;
        }
        case ZEND_AST_BINARY_OP: {
            zend_long left_val = evaluate_numeric_expression(expr->child[0]);
            zend_long right_val = evaluate_numeric_expression(expr->child[1]);
            switch (expr->attr) {
                case ZEND_ADD:  // +
                    return left_val + right_val;
                case ZEND_SUB:  // -
                    return left_val - right_val;
                case ZEND_MUL:  // *
                    return left_val * right_val;
                case ZEND_DIV:  // /
                    return right_val != 0 ? left_val / right_val : 0;
                case ZEND_MOD:  // %
                    return right_val != 0 ? left_val % right_val : 0;
                default:
                    return 0;
            }
        }
        default:
            return 0;
    }
}

// 将数字转换为字符串
static zend_string* number_to_string(zend_long num) {
    char buf[64];
    snprintf(buf, sizeof(buf), "%ld", num);
    return zend_string_init(buf, strlen(buf), 0);
}

static zend_string* evaluate_concat_expression(zend_ast *expr) {
    if (!expr) return NULL;
    
    // 尝试评估左侧为字符串
    zend_string *left = evaluate_string_expression(expr->child[0]);
    // 如果左侧不是字符串，尝试评估为数字并转换为字符串
    if (!left && expr->child[0]) {
        zend_long left_num = evaluate_numeric_expression(expr->child[0]);
        // 检查是否是数字表达式（ZEND_AST_BINARY_OP 且是算术运算）
        if (expr->child[0]->kind == ZEND_AST_BINARY_OP) {
            uint32_t op = expr->child[0]->attr;
            if (op == ZEND_ADD || op == ZEND_SUB || op == ZEND_MUL || op == ZEND_DIV || op == ZEND_MOD) {
                left = number_to_string(left_num);
            }
        } else {
            // 对于其他类型，也尝试转换
            left = number_to_string(left_num);
        }
    }
    
    // 尝试评估右侧为字符串
    zend_string *right = evaluate_string_expression(expr->child[1]);
    // 如果右侧不是字符串，尝试评估为数字并转换为字符串
    if (!right && expr->child[1]) {
        zend_long right_num = evaluate_numeric_expression(expr->child[1]);
        // 检查是否是数字表达式（ZEND_AST_BINARY_OP 且是算术运算）
        if (expr->child[1]->kind == ZEND_AST_BINARY_OP) {
            uint32_t op = expr->child[1]->attr;
            if (op == ZEND_ADD || op == ZEND_SUB || op == ZEND_MUL || op == ZEND_DIV || op == ZEND_MOD) {
                right = number_to_string(right_num);
            }
        } else {
            // 对于其他类型，也尝试转换
            right = number_to_string(right_num);
        }
    }
    
    if (!left || !right) {
        if (left) zend_string_release(left);
        if (right) zend_string_release(right);
        return NULL;
    }
    size_t new_len = ZSTR_LEN(left) + ZSTR_LEN(right);
    zend_string *result = zend_string_alloc(new_len, 0);
    memcpy(ZSTR_VAL(result), ZSTR_VAL(left), ZSTR_LEN(left));
    memcpy(ZSTR_VAL(result) + ZSTR_LEN(left), ZSTR_VAL(right), ZSTR_LEN(right));
    ZSTR_VAL(result)[new_len] = '\0';
    zend_string_release(left);
    zend_string_release(right);
    return result;
}

// 评估字符串异或操作 (^)
static zend_string* evaluate_xor_expression(zend_ast *expr) {
    if (!expr) return NULL;
    zend_string *left = evaluate_string_expression(expr->child[0]);
    zend_string *right = evaluate_string_expression(expr->child[1]);
    if (!left || !right) {
        if (left) zend_string_release(left);
        if (right) zend_string_release(right);
        return NULL;
    }
    // 取较短字符串的长度
    size_t len = ZSTR_LEN(left) < ZSTR_LEN(right) ? ZSTR_LEN(left) : ZSTR_LEN(right);
    if (len == 0) {
        zend_string_release(left);
        zend_string_release(right);
        return NULL;
    }
    zend_string *result = zend_string_alloc(len, 0);
    for (size_t i = 0; i < len; i++) {
        ZSTR_VAL(result)[i] = ZSTR_VAL(left)[i] ^ ZSTR_VAL(right)[i];
    }
    ZSTR_VAL(result)[len] = '\0';
    zend_string_release(left);
    zend_string_release(right);
    return result;
}

// 评估字符串按位或操作 (|)
static zend_string* evaluate_or_expression(zend_ast *expr) {
    if (!expr) return NULL;
    zend_string *left = evaluate_string_expression(expr->child[0]);
    zend_string *right = evaluate_string_expression(expr->child[1]);
    if (!left || !right) {
        if (left) zend_string_release(left);
        if (right) zend_string_release(right);
        return NULL;
    }
    // 取较短字符串的长度
    size_t len = ZSTR_LEN(left) < ZSTR_LEN(right) ? ZSTR_LEN(left) : ZSTR_LEN(right);
    if (len == 0) {
        zend_string_release(left);
        zend_string_release(right);
        return NULL;
    }
    zend_string *result = zend_string_alloc(len, 0);
    for (size_t i = 0; i < len; i++) {
        ZSTR_VAL(result)[i] = ZSTR_VAL(left)[i] | ZSTR_VAL(right)[i];
    }
    ZSTR_VAL(result)[len] = '\0';
    zend_string_release(left);
    zend_string_release(right);
    return result;
}

// 评估字符串按位与操作 (&)
static zend_string* evaluate_and_expression(zend_ast *expr) {
    if (!expr) return NULL;
    zend_string *left = evaluate_string_expression(expr->child[0]);
    zend_string *right = evaluate_string_expression(expr->child[1]);
    if (!left || !right) {
        if (left) zend_string_release(left);
        if (right) zend_string_release(right);
        return NULL;
    }
    // 取较短字符串的长度
    size_t len = ZSTR_LEN(left) < ZSTR_LEN(right) ? ZSTR_LEN(left) : ZSTR_LEN(right);
    if (len == 0) {
        zend_string_release(left);
        zend_string_release(right);
        return NULL;
    }
    zend_string *result = zend_string_alloc(len, 0);
    for (size_t i = 0; i < len; i++) {
        ZSTR_VAL(result)[i] = ZSTR_VAL(left)[i] & ZSTR_VAL(right)[i];
    }
    ZSTR_VAL(result)[len] = '\0';
    zend_string_release(left);
    zend_string_release(right);
    return result;
}

static zend_string* evaluate_strtr_strings(zend_string *input, zend_string *from, zend_string *to) {
    if (!input || !from || !to) {
        return NULL;
    }
    size_t map_len = ZSTR_LEN(from) < ZSTR_LEN(to) ? ZSTR_LEN(from) : ZSTR_LEN(to);
    if (map_len == 0) {
        return zend_string_copy(input);
    }
    zend_string *result = zend_string_init(ZSTR_VAL(input), ZSTR_LEN(input), 0);
    char *res = ZSTR_VAL(result);
    const char *from_val = ZSTR_VAL(from);
    const char *to_val = ZSTR_VAL(to);
    for (size_t i = 0; i < ZSTR_LEN(result); i++) {
        for (size_t j = 0; j < map_len; j++) {
            if (res[i] == from_val[j]) {
                res[i] = to_val[j];
                break;
            }
        }
    }
    return result;
}

static zend_string* evaluate_strtr_call(zend_ast *call_ast) {
    if (!call_ast) return NULL;
    zend_ast *args_ast = call_ast->child[1];
    if (!args_ast || !zend_ast_is_list(args_ast)) {
        return NULL;
    }
    zend_ast_list *args = zend_ast_get_list(args_ast);
    if (!args || args->children != 3 || !args->child) {
        return NULL;
    }
    zend_string *input = evaluate_string_expression(args->child[0]);
    zend_string *from = evaluate_string_expression(args->child[1]);
    zend_string *to = evaluate_string_expression(args->child[2]);
    if (!input || !from || !to) {
        if (input) zend_string_release(input);
        if (from) zend_string_release(from);
        if (to) zend_string_release(to);
        return NULL;
    }
    zend_string *result = evaluate_strtr_strings(input, from, to);
    zend_string_release(input);
    zend_string_release(from);
    zend_string_release(to);
    return result;
}

static zend_string* string_replace_all(zend_string *subject, zend_string *search, zend_string *replace) {
    if (!subject || !search || !replace || ZSTR_LEN(search) == 0) {
        return NULL;
    }
    const char *subject_val = ZSTR_VAL(subject);
    const char *search_val = ZSTR_VAL(search);
    size_t subject_len = ZSTR_LEN(subject);
    size_t search_len = ZSTR_LEN(search);
    size_t replace_len = ZSTR_LEN(replace);
    size_t count = 0;
    const char *cursor = subject_val;
    const char *end = subject_val + subject_len;
    while (cursor < end) {
        const char *found = strstr(cursor, search_val);
        if (!found) break;
        count++;
        cursor = found + search_len;
    }
    if (count == 0) {
        return zend_string_copy(subject);
    }
    size_t new_len = subject_len + count * (replace_len - search_len);
    zend_string *result = zend_string_alloc(new_len, 0);
    char *dst = ZSTR_VAL(result);
    cursor = subject_val;
    while (cursor < end) {
        const char *found = strstr(cursor, search_val);
        if (!found) {
            size_t remaining = end - cursor;
            memcpy(dst, cursor, remaining);
            dst += remaining;
            break;
        }
        size_t chunk = found - cursor;
        memcpy(dst, cursor, chunk);
        dst += chunk;
        memcpy(dst, ZSTR_VAL(replace), replace_len);
        dst += replace_len;
        cursor = found + search_len;
    }
    dst[0] = '\0';
    return result;
}

static zend_string* url_decode_string(zend_string *input, zend_bool raw) {
    if (!input) return NULL;
    zend_string *result = zend_string_alloc(ZSTR_LEN(input), 0);
    char *dst = ZSTR_VAL(result);
    const char *src = ZSTR_VAL(input);
    size_t len = ZSTR_LEN(input);
    size_t i = 0;
    while (i < len) {
        unsigned char c = (unsigned char)src[i];
        if (!raw && c == '+') {
            *dst++ = ' ';
            i++;
            continue;
        }
        if (c == '%' && i + 2 < len) {
            unsigned char high = (unsigned char)src[i + 1];
            unsigned char low = (unsigned char)src[i + 2];
            if (isxdigit(high) && isxdigit(low)) {
                char hex[3] = {(char)high, (char)low, '\0'};
                *dst++ = (char)strtol(hex, NULL, 16);
                i += 3;
                continue;
            }
        }
        *dst++ = (char)c;
        i++;
    }
    size_t out_len = dst - ZSTR_VAL(result);
    ZSTR_VAL(result)[out_len] = '\0';
    return zend_string_truncate(result, out_len, 0);
}

static zend_string* rot13_string(zend_string *input) {
    if (!input) return NULL;
    zend_string *result = zend_string_init(ZSTR_VAL(input), ZSTR_LEN(input), 0);
    char *val = ZSTR_VAL(result);
    for (size_t i = 0; i < ZSTR_LEN(result); i++) {
        unsigned char ch = (unsigned char)val[i];
        if (ch >= 'a' && ch <= 'z') {
            val[i] = 'a' + (ch - 'a' + 13) % 26;
        } else if (ch >= 'A' && ch <= 'Z') {
            val[i] = 'A' + (ch - 'A' + 13) % 26;
        }
    }
    return result;
}

static zend_string* base64_decode_string(zend_string *input) {
    if (!input) return NULL;
    static const signed char decode_table[256] = {
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,62,-1,-1,-1,63,
        52,53,54,55,56,57,58,59,60,61,-1,-1,-1,-2,-1,-1,
        -1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,
        15,16,17,18,19,20,21,22,23,24,25,-1,-1,-1,-1,-1,
        -1,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,
        41,42,43,44,45,46,47,48,49,50,51,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,
        -1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1,-1
    };
    size_t in_len = ZSTR_LEN(input);
    zend_string *result = zend_string_alloc((in_len / 4 + 1) * 3, 0);
    unsigned char *out = (unsigned char*)ZSTR_VAL(result);
    size_t out_len = 0;
    int val = 0;
    int bits = -8;
    const unsigned char *data = (const unsigned char*)ZSTR_VAL(input);
    for (size_t i = 0; i < in_len; i++) {
        signed char d = decode_table[data[i]];
        if (d == -1) {
            continue;
        }
        if (d == -2) {
            break;
        }
        val = (val << 6) + d;
        bits += 6;
        if (bits >= 0) {
            out[out_len++] = (unsigned char)((val >> bits) & 0xFF);
            bits -= 8;
        }
    }
    ZSTR_VAL(result)[out_len] = '\0';
    return zend_string_truncate(result, out_len, 0);
}


static zend_string* evaluate_string_call(zend_ast *call_ast) {
    if (!call_ast) return NULL;
    zend_ast *name_node = call_ast->child[0];
    if (!name_node || name_node->kind != ZEND_AST_ZVAL) {
        return NULL;
    }
    zval *zv = zend_ast_get_zval(name_node);
    if (!zv || Z_TYPE_P(zv) != IS_STRING) {
        return NULL;
    }
    zend_string *func_name = zend_ast_get_str(name_node);
    if (!func_name) {
        return NULL;
    }
    if (zend_string_equals_literal_ci(func_name, "strtr")) {
        return evaluate_strtr_call(call_ast);
    }
    if (zend_string_equals_literal_ci(func_name, "strrev")) {
        zend_ast *args_ast = call_ast->child[1];
        if (!args_ast || !zend_ast_is_list(args_ast)) {
            return NULL;
        }
        zend_ast_list *args = zend_ast_get_list(args_ast);
        if (!args || args->children != 1 || !args->child) {
            return NULL;
        }
        zend_string *value = evaluate_string_expression(args->child[0]);
        if (!value) {
            return NULL;
        }
        zend_string *result = zend_string_alloc(ZSTR_LEN(value), 0);
        char *res = ZSTR_VAL(result);
        for (size_t i = 0; i < ZSTR_LEN(value); i++) {
            res[i] = ZSTR_VAL(value)[ZSTR_LEN(value) - 1 - i];
        }
        res[ZSTR_LEN(value)] = '\0';
        zend_string_release(value);
        return result;
    }
    if (zend_string_equals_literal_ci(func_name, "strtolower")) {
        zend_ast *args_ast = call_ast->child[1];
        if (!args_ast || !zend_ast_is_list(args_ast)) {
            return NULL;
        }
        zend_ast_list *args = zend_ast_get_list(args_ast);
        if (!args || args->children != 1 || !args->child) {
            return NULL;
        }
        zend_string *value = evaluate_string_expression(args->child[0]);
        if (!value) {
            return NULL;
        }
        zend_string *result = zend_string_init(ZSTR_VAL(value), ZSTR_LEN(value), 0);
        for (size_t i = 0; i < ZSTR_LEN(result); i++) {
            ZSTR_VAL(result)[i] = tolower((unsigned char)ZSTR_VAL(result)[i]);
        }
        zend_string_release(value);
        return result;
    }
    if (zend_string_equals_literal_ci(func_name, "str_replace")) {
        return evaluate_str_replace_call(call_ast);
    }
    if (zend_string_equals_literal_ci(func_name, "base64_decode")) {
        return evaluate_base64_decode_call(call_ast);
    }
    if (zend_string_equals_literal_ci(func_name, "urldecode")) {
        return evaluate_url_decode_call(call_ast, 0);
    }
    if (zend_string_equals_literal_ci(func_name, "rawurldecode")) {
        return evaluate_url_decode_call(call_ast, 1);
    }
    if (zend_string_equals_literal_ci(func_name, "str_rot13")) {
        return evaluate_rot13_call(call_ast);
    }
    return NULL;
}

static zend_string* evaluate_str_replace_call(zend_ast *call_ast) {
    zend_ast *args_ast = call_ast->child[1];
    if (!args_ast || !zend_ast_is_list(args_ast)) {
        return NULL;
    }
    zend_ast_list *args = zend_ast_get_list(args_ast);
    if (!args || args->children < 3 || !args->child) {
        return NULL;
    }
    zend_string *search = evaluate_string_expression(args->child[0]);
    zend_string *replace = evaluate_string_expression(args->child[1]);
    zend_string *subject = evaluate_string_expression(args->child[2]);
    if (!search || !replace || !subject) {
        if (search) zend_string_release(search);
        if (replace) zend_string_release(replace);
        if (subject) zend_string_release(subject);
        return NULL;
    }
    zend_string *result = string_replace_all(subject, search, replace);
    zend_string_release(search);
    zend_string_release(replace);
    zend_string_release(subject);
    return result;
}

static zend_string* evaluate_base64_decode_call(zend_ast *call_ast) {
    zend_ast *args_ast = call_ast->child[1];
    if (!args_ast || !zend_ast_is_list(args_ast)) {
        return NULL;
    }
    zend_ast_list *args = zend_ast_get_list(args_ast);
    if (args->children < 1) {
        return NULL;
    }
    zend_string *value = evaluate_string_expression(args->child[0]);
    if (!value) {
        return NULL;
    }
    zend_string *result = base64_decode_string(value);
    zend_string_release(value);
    return result;
}

static zend_string* evaluate_url_decode_call(zend_ast *call_ast, zend_bool raw) {
    zend_ast *args_ast = call_ast->child[1];
    if (!args_ast || !zend_ast_is_list(args_ast)) {
        return NULL;
    }
    zend_ast_list *args = zend_ast_get_list(args_ast);
    if (args->children < 1) {
        return NULL;
    }
    zend_string *value = evaluate_string_expression(args->child[0]);
    if (!value) {
        return NULL;
    }
    zend_string *result = url_decode_string(value, raw);
    zend_string_release(value);
    return result;
}

static zend_string* evaluate_rot13_call(zend_ast *call_ast) {
    zend_ast *args_ast = call_ast->child[1];
    if (!args_ast || !zend_ast_is_list(args_ast)) {
        return NULL;
    }
    zend_ast_list *args = zend_ast_get_list(args_ast);
    if (args->children < 1) {
        return NULL;
    }
    zend_string *value = evaluate_string_expression(args->child[0]);
    if (!value) {
        return NULL;
    }
    zend_string *result = rot13_string(value);
    zend_string_release(value);
    return result;
}

static zend_string* evaluate_string_expression(zend_ast *expr) {
    if (!expr) return NULL;
    switch (expr->kind) {
        case ZEND_AST_ZVAL: {
            zval *zv = zend_ast_get_zval(expr);
            if (!zv) return NULL;
            if (Z_TYPE_P(zv) == IS_STRING) {
                return zend_string_copy(Z_STR_P(zv));
            } else if (Z_TYPE_P(zv) == IS_LONG) {
                return number_to_string(Z_LVAL_P(zv));
            } else if (Z_TYPE_P(zv) == IS_DOUBLE) {
                return number_to_string((zend_long)Z_DVAL_P(zv));
            }
            return NULL;
        }
        case ZEND_AST_VAR: {
            // 支持变量引用，如 $a, $s 等
            zend_ast *name_node = expr->child[0];
            if (!name_node || name_node->kind != ZEND_AST_ZVAL) {
                return NULL;
            }
            zval *zv = zend_ast_get_zval(name_node);
            if (!zv || Z_TYPE_P(zv) != IS_STRING) {
                return NULL;
            }
            zend_string *var_name = zend_ast_get_str(name_node);
            if (!var_name) {
                return NULL;
            }
            // 从变量值表中查找变量值
            zval *var_val = zend_hash_find(&var_value_table, var_name);
            if (var_val) {
                if (Z_TYPE_P(var_val) == IS_STRING) {
                    return zend_string_copy(Z_STR_P(var_val));
                } else if (Z_TYPE_P(var_val) == IS_LONG) {
                    return number_to_string(Z_LVAL_P(var_val));
                } else if (Z_TYPE_P(var_val) == IS_DOUBLE) {
                    return number_to_string((zend_long)Z_DVAL_P(var_val));
                }
            }
            return NULL;
        }
        case ZEND_AST_CALL:
            return evaluate_string_call(expr);
        case ZEND_AST_BINARY_OP:
            if (expr->attr == ZEND_CONCAT) {
                return evaluate_concat_expression(expr);
            } else if (expr->attr == ZEND_BW_XOR) {
                // 字符串异或操作 (^)
                return evaluate_xor_expression(expr);
            } else if (expr->attr == ZEND_BW_OR) {
                // 字符串按位或操作 (|)
                return evaluate_or_expression(expr);
            } else if (expr->attr == ZEND_BW_AND) {
                // 字符串按位与操作 (&)
                return evaluate_and_expression(expr);
            } else if (expr->attr == ZEND_ADD || expr->attr == ZEND_SUB || 
                       expr->attr == ZEND_MUL || expr->attr == ZEND_DIV || 
                       expr->attr == ZEND_MOD) {
                // 算术运算，转换为字符串
                zend_long num = evaluate_numeric_expression(expr);
                return number_to_string(num);
            }
            return NULL;
        default:
            return NULL;
    }
}

/* 统一调用图（合并静态和动态调用图） */
static HashTable merged_call_graph;

/* 建议1：合并静态和动态调用图 */
static void merge_call_graphs(void) {
    /* 初始化合并后的调用图 */
    zend_hash_init(&merged_call_graph, 8, NULL, ZVAL_PTR_DTOR, 0);
    
    /* 1. 先把 call_graph_static 拷贝进 merged */
    zend_string *caller_key;
    zval *caller_val;
    ZEND_HASH_FOREACH_STR_KEY_VAL(&call_graph_static, caller_key, caller_val) {
        if (caller_key && caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
            HashTable *static_callee_set = (HashTable *)Z_PTR_P(caller_val);
            
            /* 在 merged_call_graph 中查找或创建 caller */
            zend_string *caller_str = zend_string_copy(caller_key);
            zval *merged_caller_val = zend_hash_find(&merged_call_graph, caller_str);
            HashTable *merged_callee_set = NULL;
            
            if (merged_caller_val && Z_TYPE_P(merged_caller_val) == IS_PTR) {
                merged_callee_set = (HashTable *)Z_PTR_P(merged_caller_val);
            } else {
                merged_callee_set = (HashTable *)emalloc(sizeof(HashTable));
                zend_hash_init(merged_callee_set, 8, NULL, NULL, 1);
                
                zval new_caller_val;
                ZVAL_PTR(&new_caller_val, merged_callee_set);
                zend_hash_add(&merged_call_graph, caller_str, &new_caller_val);
            }
            
            /* 将静态调用图的 callee 添加到合并图中 */
            if (merged_callee_set && static_callee_set) {
                zend_string *callee_key;
                ZEND_HASH_FOREACH_STR_KEY(static_callee_set, callee_key) {
                    if (callee_key && !zend_hash_exists(merged_callee_set, callee_key)) {
                        zval callee_val;
                        ZVAL_LONG(&callee_val, 1);
                        zend_hash_add(merged_callee_set, callee_key, &callee_val);
                    }
                } ZEND_HASH_FOREACH_END();
            }
        }
    } ZEND_HASH_FOREACH_END();
    
    /* 2. 再把 call_graph_extra 里的边插进去（不存在就加，存在就保持） */
    ZEND_HASH_FOREACH_STR_KEY_VAL(&call_graph_extra, caller_key, caller_val) {
        if (caller_key && caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
            HashTable *extra_callee_set = (HashTable *)Z_PTR_P(caller_val);
            
            /* 在 merged_call_graph 中查找或创建 caller */
            zend_string *caller_str = zend_string_copy(caller_key);
            zval *merged_caller_val = zend_hash_find(&merged_call_graph, caller_str);
            HashTable *merged_callee_set = NULL;
            
            if (merged_caller_val && Z_TYPE_P(merged_caller_val) == IS_PTR) {
                merged_callee_set = (HashTable *)Z_PTR_P(merged_caller_val);
            } else {
                merged_callee_set = (HashTable *)emalloc(sizeof(HashTable));
                zend_hash_init(merged_callee_set, 8, NULL, NULL, 1);
                
                zval new_caller_val;
                ZVAL_PTR(&new_caller_val, merged_callee_set);
                zend_hash_add(&merged_call_graph, caller_str, &new_caller_val);
            }
            
            /* 将动态调用图的 callee 添加到合并图中 */
            if (merged_callee_set && extra_callee_set) {
                zend_string *callee_key;
                ZEND_HASH_FOREACH_STR_KEY(extra_callee_set, callee_key) {
                    if (callee_key && !zend_hash_exists(merged_callee_set, callee_key)) {
                        zval callee_val;
                        ZVAL_LONG(&callee_val, 1);
                        zend_hash_add(merged_callee_set, callee_key, &callee_val);
                    }
                } ZEND_HASH_FOREACH_END();
            }
        }
    } ZEND_HASH_FOREACH_END();
    
    printf("已合并静态和动态调用图，合并后共有 %u 个调用者\n", 
           zend_hash_num_elements(&merged_call_graph));
}

/* 全局标志：通过调用图发现的危险路径 */
static int global_dynamic_path_detected = 0;

/* 建议2：基于调用图的全局污点路径搜索 */
static int path_search_from_entry_to_sink(const char *entry_func, HashTable *visited) {
    if (!entry_func || !visited) return 0;
    
    zend_string *entry_str = zend_string_init(entry_func, strlen(entry_func), 0);
    
    /* 检查是否已访问过（避免循环） */
    if (zend_hash_exists(visited, entry_str)) {
        zend_string_release(entry_str);
        return 0;
    }
    
    /* 标记为已访问 */
    zval visit_val;
    ZVAL_LONG(&visit_val, 1);
    zend_hash_add(visited, entry_str, &visit_val);
    
    /* 在合并调用图中查找该函数的调用关系 */
    zval *caller_val = zend_hash_find(&merged_call_graph, entry_str);
    int found_sink = 0;
    
    if (caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
        HashTable *callee_set = (HashTable *)Z_PTR_P(caller_val);
        if (callee_set) {
            zend_string *callee_key;
            ZEND_HASH_FOREACH_STR_KEY(callee_set, callee_key) {
                if (callee_key) {
                    /* 检查是否是危险函数（sink） */
                    if (is_known_sink_function(callee_key)) {
                        printf("发现从入口 %s 到危险函数 %s 的调用路径（通过调用图）\n", 
                               entry_func, ZSTR_VAL(callee_key));
                        found_sink = 1;
                        // 直接设置全局标志，确保检测到
                        global_dynamic_path_detected = 1;
                        break;  // 找到后立即退出
                    } else {
                        /* 递归搜索 */
                        found_sink = path_search_from_entry_to_sink(ZSTR_VAL(callee_key), visited);
                        if (found_sink) {
                            // 递归搜索找到后也设置标志
                            global_dynamic_path_detected = 1;
                            break;
                        }
                    }
                }
            } ZEND_HASH_FOREACH_END();
        }
    }
    
    zend_string_release(entry_str);
    return found_sink;
}

/* 建议2：全局污点分析（利用合并后的调用图） */
static void global_taint_analysis_with_cg(void) {
    printf("开始基于调用图的全局污点分析...\n");
    
    /* 入口点：__main__ 或已知的源函数 */
    const char *entry_points[] = {"__main__"};
    size_t num_entries = sizeof(entry_points) / sizeof(entry_points[0]);
    
    HashTable visited;
    zend_hash_init(&visited, 8, NULL, NULL, 1);
    
    for (size_t i = 0; i < num_entries; i++) {
        if (path_search_from_entry_to_sink(entry_points[i], &visited)) {
            printf("警告：通过动态补充的调用图，发现从 %s 到危险函数的路径\n", 
                   entry_points[i]);
            global_dynamic_path_detected = 1;  /* 设置全局标志 */
        }
    }
    
    zend_hash_destroy(&visited);
}

/* 构建静态调用图：收集静态可解析的函数调用 */
static void build_static_call_graph(zend_ast *ast) {
    if (!ast) return;
    Stack *stack = (Stack *)malloc(sizeof(Stack));
    initStack(stack, 10000);  // 增加栈大小以处理大型AST
    push(stack, ast);
    
    zend_string *current_caller = NULL;  // 当前函数名
    
    while (!isEmpty(stack)) {
        zend_ast *current = pop(stack);
        if (!current) continue;
        
        /* 跟踪当前函数名 */
        if (current->kind == ZEND_AST_FUNC_DECL || current->kind == ZEND_AST_METHOD) {
            zend_ast_decl *decl = (zend_ast_decl *)current;
            if (decl->name) {
                if (current_caller) {
                    zend_string_release(current_caller);
                }
                current_caller = zend_string_copy(decl->name);
            }
        }
        
        /* 收集静态可解析的函数调用（函数名是直接字符串，不是变量） */
        if (current->kind == ZEND_AST_CALL) {
            zend_ast *func_ast = current->child[0];
            if (func_ast && func_ast->kind == ZEND_AST_ZVAL) {
                zval *zv = zend_ast_get_zval(func_ast);
                if (zv && Z_TYPE_P(zv) == IS_STRING) {
                    zend_string *callee = zend_ast_get_str(func_ast);
                    const char *caller_name = current_caller ? ZSTR_VAL(current_caller) : "__main__";
                    
                    zend_string *caller_str = zend_string_init(caller_name, strlen(caller_name), 0);
                    
                    /* 检查 call_graph_static 中是否已有该 caller */
                    zval *caller_val = zend_hash_find(&call_graph_static, caller_str);
                    HashTable *callee_set = NULL;
                    
                    if (caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
                        callee_set = (HashTable *)Z_PTR_P(caller_val);
                    } else {
                        /* 创建新的 callee 集合 */
                        callee_set = (HashTable *)emalloc(sizeof(HashTable));
                        zend_hash_init(callee_set, 8, NULL, NULL, 1);
                        
                        zval new_caller_val;
                        ZVAL_PTR(&new_caller_val, callee_set);
                        zend_hash_add(&call_graph_static, caller_str, &new_caller_val);
                    }
                    
                    /* 将 callee 添加到集合中 */
                    if (callee_set) {
                        zval callee_val;
                        ZVAL_LONG(&callee_val, 1);
                        zend_hash_add(callee_set, callee, &callee_val);
                    }
                    
                    zend_string_release(caller_str);
                }
            }
        }
        
        uint32_t count = 0;
        zend_ast **children = ast_get_children(current, &count);
        for (uint32_t i = 0; i < count; i++) {
            if (children[i]) {
                push(stack, children[i]);
            }
        }
    }
    
    if (current_caller) {
        zend_string_release(current_caller);
    }
    
    free(stack->data);
    free(stack);
}

static void dynamic_function_analysis(zend_ast *ast) {
    if (!ast) return;
    Stack *stack = (Stack *)malloc(sizeof(Stack));
    initStack(stack, 10000);  // 增加栈大小以处理大型AST
    push(stack, ast);
    while (!isEmpty(stack)) {
        zend_ast *current = pop(stack);
        if (!current) continue;
        
        /* 跟踪当前函数名（用于记录调用者） */
        if (current->kind == ZEND_AST_FUNC_DECL || current->kind == ZEND_AST_METHOD) {
            zend_ast_decl *decl = (zend_ast_decl *)current;
            if (decl->name) {
                if (current_function_name) {
                    zend_string_release(current_function_name);
                }
                current_function_name = zend_string_copy(decl->name);
            }
        }
        
        if (current->kind == ZEND_AST_ASSIGN) {
            zend_ast *var_node = current->child[0];
            zend_ast *expr_node = current->child[1];
            if (var_node && expr_node) {
                zend_string *resolved = evaluate_string_expression(expr_node);
                if (resolved) {
                    if (is_known_sink_function(resolved)) {
                        add_sink_var_from_assignment(var_node, resolved);
                        printf("静态识别危险函数变量: 通过字符串表达式求值得到 %s\n", ZSTR_VAL(resolved));
                    }
                    zend_string_release(resolved);
                } else {
                    /* 如果表达式包含位运算（异或、按位或、按位与），可能是混淆的代码
                     * 尝试检测是否可能是危险函数名 */
                    if (expr_node->kind == ZEND_AST_BINARY_OP) {
                        // 检查是否是位运算操作
                        if (expr_node->attr == ZEND_BW_XOR || 
                            expr_node->attr == ZEND_BW_OR || 
                            expr_node->attr == ZEND_BW_AND) {
                            // 对于混淆代码，即使无法静态求值，也应该标记为可疑
                            // 如果变量后续被用于函数调用，应该被检测
                            if (var_node->kind == ZEND_AST_VAR) {
                                // 标记这个变量为可疑，需要动态检测
                                var_node->tainted |= AST_NEED_DYNAMIC_RESOLVE;
                                printf("警告: 检测到可能混淆的函数名赋值（包含位运算），变量需要动态检测\n");
                            }
                        }
                    }
                    /* TODO 3: 静态搞不定，标记为需要动态解析 */
                    /* 如果 var_node 是变量，标记它需要动态解析 */
                    if (var_node->kind == ZEND_AST_VAR) {
                        var_node->tainted |= AST_NEED_DYNAMIC_RESOLVE;
                    }
                }
            }
        }
        uint32_t count = 0;
        zend_ast **children = ast_get_children(current, &count);
        for (uint32_t i = 0; i < count; i++) {
            if (children[i]) {
                push(stack, children[i]);
            }
        }
    }
    free(stack->data);
    free(stack);
}

//对各个可能产生危险的语法节点进行assert插入检测
void traverse_and_modify_ast(zend_ast *ast, zend_arena **ast_arena, HashTable *var_table) {
    Stack* stack = (Stack*)malloc(sizeof(Stack));
    initStack(stack, 10000);  // 增加栈大小以处理大型AST
    push(stack, ast);

    while (!isEmpty(stack)) {
        zend_ast* current = pop(stack);
        if (!current) continue;
        
        // 验证 current 节点是否仍然有效
        if (current->kind > 1000) {
            continue;  // 跳过无效的节点类型
        }

        int ast_modified = 0;  // 标记AST是否被修改

        /* 1) 函数调用相关：$var() / $arr['x']() 插桩 */
        if (current->kind == ZEND_AST_CALL) {
            zend_ast *func_ast = current->child[0];
            if (!func_ast) {
                // 继续遍历子节点
                uint32_t count = 0;
                zend_ast **children = ast_get_children(current, &count);
                for (uint32_t i = 0; i < count; i++) {
                    if (children[i]) push(stack, children[i]);
                }
                continue;
            }

            /* 1.1 $var() 形式 - 动态函数调用 */
            if (func_ast->kind == ZEND_AST_VAR) {
                // 安全地获取 parent，检查 current 是否仍然有效
                zend_ast *parent = NULL;
                if (current && current->father) {
                    parent = current->father;
                    // 验证 parent 是否仍然有效（检查它是否仍然是有效的 AST 节点）
                    if (parent->kind > 1000) {
                        parent = NULL;  // 无效的节点类型
                    }
                }
                if (!parent || parent->kind != ZEND_AST_STMT_LIST) {
                    // 继续遍历子节点
                    uint32_t count = 0;
                    zend_ast **children = ast_get_children(current, &count);
                    for (uint32_t i = 0; i < count; i++) {
                        if (children[i]) push(stack, children[i]);
                    }
                    continue;
                }
                
                /* 建议3：根据 AST_NEED_DYNAMIC_RESOLVE 标记决定是否插桩 */
                bool should_instrument = true;
                if (func_ast->tainted & AST_NEED_DYNAMIC_RESOLVE) {
                    /* 静态搞不定的变量，需要动态解析，应该插桩 */
                    printf("检测到需要动态解析的变量函数调用，将进行插桩\n");
                    should_instrument = true;
                } else {
                    /* 静态能解析的变量，可以选择不插桩或插简单日志 */
                    /* 为了保持兼容性，这里仍然插桩，但可以添加标记 */
                    should_instrument = true;
                }
                
                const char *var_name = get_var_name(func_ast);
                if (var_name && should_instrument) {
                    zend_ast_list *list = zend_ast_get_list(parent);
                    if (!list) {
                        // 继续遍历子节点
                        uint32_t count = 0;
                        zend_ast **children = ast_get_children(current, &count);
                        for (uint32_t i = 0; i < count; i++) {
                            if (children[i]) push(stack, children[i]);
                        }
                        continue;
                    }
                    
                    for (uint32_t i = 0; i < list->children; i++) {
                        if (list->child[i] == current) {
                            zend_ast *new_list = insert_assert_before_at_index(
                                parent, i, ast_arena, (char*)var_name);
                            if (new_list && new_list != parent) {
                                // insert_assert_before_at_index 已经更新了所有子节点的 father 指针
                                // 包括 current 节点，所以 current->father 应该已经指向 new_list 了
                                
                                // 重要：在替换 parent 之前，确保 current->father 已经正确更新
                                // 因为 replace_child_in_parent 可能会访问 parent->father
                                zend_ast_list *new_list_ptr = zend_ast_get_list(new_list);
                                if (new_list_ptr && i + 1 < new_list_ptr->children) {
                                    // current 在新列表中的位置是 i+1（因为我们在 i 位置插入了新节点）
                                    if (new_list_ptr->child[i + 1] == current) {
                                        // 确保 current->father 指向 new_list
                                        current->father = new_list;
                                    }
                                }
                                
                                // 现在安全地替换 parent
                                if (parent->father) {
                                    replace_child_in_parent(parent->father, parent, new_list);
                                } else {
                                    g_root_ast = new_list;
                                }
                                
                                // 重要：修改 AST 后，不要继续访问 current 或 parent
                                ast_modified = 1;
                                break;  // 立即退出循环
                            }
                            break;
                        }
                    }
                }
                /* 处理完动态函数调用后，跳过后续的静态函数处理 */
                if (ast_modified) {
                    continue;
                }
            }
            /* 1.2 $arr['x']() 形式 */
            else if (func_ast->kind == ZEND_AST_DIM) {
                zend_ast *dim_var = func_ast->child[0];
                if (!dim_var) {
                    // 继续遍历子节点
                    uint32_t count = 0;
                    zend_ast **children = ast_get_children(current, &count);
                    for (uint32_t i = 0; i < count; i++) {
                        if (children[i]) push(stack, children[i]);
                    }
                    continue;
                }
                
                const char *var_name = get_var_name(dim_var);
                if (var_name) {
                    char tmp_var_name[32];
                    snprintf(tmp_var_name, sizeof(tmp_var_name), "__tmp_");
                    strncat(tmp_var_name, var_name, sizeof(tmp_var_name) - strlen(tmp_var_name) - 1);

                    zend_ast *assign_ast = deep_copy_dim_to_var(func_ast, ast_arena, tmp_var_name);
                    zend_ast *parent = current->father;
                    if (parent && parent->kind == ZEND_AST_STMT_LIST) {
                        zend_ast_list *list = zend_ast_get_list(parent);
                        if (list) {
                            for (uint32_t i = 0; i < list->children; i++) {
                                if (list->child[i] == current) {
                                    // 先插入赋值，再插入断言
                                    zend_ast *new_list = insert_stmt_before_at_index(
                                        parent, i, assign_ast, ast_arena);
                                    if (new_list && new_list != parent) {
                                        // insert_stmt_before_at_index 已经更新了所有子节点的 father 指针
                                        // 包括 current 节点，所以 current->father 已经指向 new_list 了
                                        
                                        new_list = insert_assert_before_at_index(
                                            new_list, i + 1, ast_arena, tmp_var_name);
                                        if (new_list) {
                                            // insert_assert_before_at_index 已经更新了所有子节点的 father 指针
                                            // 包括 current 节点，所以 current->father 已经指向 new_list 了
                                            
                                            if (parent->father) {
                                                replace_child_in_parent(parent->father, parent, new_list);
                                            } else {
                                                g_root_ast = new_list;
                                            }
                                            ast_modified = 1;
                                        }
                                    }
                                    break;
                                }
                            }
                        }
                    }
                }
                /* 处理完数组形式动态调用后，跳过后续的静态函数处理 */
                if (ast_modified) {
                    continue;
                }
            }
            /* 1.3 静态已知危险函数调用（如 eval, system, assert 等）—— 统一插入 assert probe */
            else if (func_ast->kind == ZEND_AST_ZVAL) {
                zval *zv = zend_ast_get_zval(func_ast);
                if (zv && Z_TYPE_P(zv) == IS_STRING) {
                    zend_string *func_name = zend_ast_get_str(func_ast);
                    /* 检查是否是已知的危险函数 */
                    if (is_known_sink_function(func_name)) {
                        /* 找到所在语句和语句列表 */
                        zend_ast *stmt_list_ast = NULL;
                        zend_ast *stmt_ast = find_stmt_and_list_for_node(current, &stmt_list_ast);
                        
                        if (stmt_ast && stmt_list_ast && stmt_list_ast->kind == ZEND_AST_STMT_LIST) {
                            zend_ast_list *list = zend_ast_get_list(stmt_list_ast);
                            if (list) {
                                for (uint32_t i = 0; i < list->children; i++) {
                                    if (list->child[i] == stmt_ast) {
                                        /* 获取第一个参数（如果有） */
                                        zend_ast *first_arg = NULL;
                                        if (current->child[1] && current->child[1]->kind == ZEND_AST_ARG_LIST) {
                                            zend_ast_list *args = zend_ast_get_list(current->child[1]);
                                            if (args && args->children > 0 && args->child) {
                                                first_arg = args->child[0];
                                            }
                                        }
                                        
                                        /* 构造 __yz_runtime_probe("sink_call", __FILE__, __LINE__, __FUNCTION__, func_name, first_arg) */
                                        /* 先构造函数名字符串节点 */
                                        zval *func_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
                                        ZVAL_STR(func_name_zv, zend_string_copy(func_name));
                                        zend_ast *func_name_ast = (zend_ast *)my_create_zval_ast_arena(func_name_zv, NULL, ast_arena);
                                        
                                        zend_ast *probe_call = build_probe_call_for_call_ast(
                                            current,
                                            ast_arena,
                                            "sink_call",
                                            func_name_ast,  // callee_ast，函数名
                                            first_arg       // first_arg_ast，第一个参数
                                        );
                                        
                                        if (probe_call) {
                                            /* 构造 assert(__yz_runtime_probe(...)) */
                                            zval *assert_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
                                            ZVAL_STR(assert_name_zv, zend_string_init("assert", 6, 0));
                                            zend_ast *assert_name_ast = (zend_ast *)my_create_zval_ast_arena(assert_name_zv, NULL, ast_arena);
                                            
                                            zend_ast_list *assert_args = my_create_ast_list_arena(1, ZEND_AST_ARG_LIST, ast_arena);
                                            assert_args->child[0] = probe_call;
                                            
                                            zend_ast *assert_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
                                                assert_name_ast, (zend_ast*)assert_args);
                                            
                                            /* 把 assert 语句插入到这条语句之前 */
                                            zend_ast *new_list = insert_stmt_before_at_index(stmt_list_ast, i, assert_call, ast_arena);
                                            
                                            /* 用新的 stmt_list 替换原来的 */
                                            if (new_list && new_list != stmt_list_ast) {
                                                new_list->father = stmt_list_ast->father;
                                                
                                                if (stmt_list_ast->father) {
                                                    replace_child_in_parent(stmt_list_ast->father, stmt_list_ast, new_list);
                                                } else {
                                                    g_root_ast = new_list;
                                                }
                                                ast_modified = 1;
                                                printf("已为危险函数 %s 插入断言探针\n", ZSTR_VAL(func_name));
                                            }
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                        /* 处理完静态危险函数后，标记已修改，跳过后续处理 */
                        if (ast_modified) {
                            continue;
                        }
                    }
                }
            }
        }
        /* 3) eval/include 相关断言插桩 —— 使用 assert(__yz_runtime_probe(...)) */
        else if (current->kind == ZEND_AST_INCLUDE_OR_EVAL) {
            // 找到"所在语句"以及它的语句列表
            zend_ast *stmt_list_ast = NULL;
            zend_ast *stmt_ast = find_stmt_and_list_for_node(current, &stmt_list_ast);

            if (stmt_ast && stmt_list_ast && stmt_list_ast->kind == ZEND_AST_STMT_LIST) {
                zend_ast_list *list = zend_ast_get_list(stmt_list_ast);
                if (list) {
                    for (uint32_t i = 0; i < list->children; i++) {
                        if (list->child[i] == stmt_ast) {
                            /* 获取 eval 的参数（代码字符串） */
                            zend_ast *eval_arg = NULL;
                            if (current->child && current->child[0]) {
                                eval_arg = current->child[0];
                            }
                            
                            /* 构造 __yz_runtime_probe("eval", __FILE__, __LINE__, __FUNCTION__, $code_str) */
                            zend_ast *probe_call = build_probe_call_for_call_ast(
                                current,
                                ast_arena,
                                "eval",
                                NULL,      // callee_ast，eval 不需要
                                eval_arg   // first_arg_ast，eval 的代码字符串
                            );
                            
                            if (probe_call) {
                                /* 构造 assert(__yz_runtime_probe(...)) */
                                zval *assert_name_zv = (zval *)zend_arena_alloc(ast_arena, sizeof(zval));
                                ZVAL_STR(assert_name_zv, zend_string_init("assert", 6, 0));
                                zend_ast *assert_name_ast = (zend_ast *)my_create_zval_ast_arena(assert_name_zv, NULL, ast_arena);
                                
                                zend_ast_list *assert_args = my_create_ast_list_arena(1, ZEND_AST_ARG_LIST, ast_arena);
                                assert_args->child[0] = probe_call;
                                
                                zend_ast *assert_call = my_ast_create_ex_arena(ZEND_AST_CALL, 2, ast_arena,
                                    assert_name_ast, (zend_ast*)assert_args);
                                
                                /* 把 assert 语句插入到这条语句之前 */
                                zend_ast *new_list = insert_stmt_before_at_index(stmt_list_ast, i, assert_call, ast_arena);

                                /* 用新的 stmt_list 替换原来的 */
                                if (new_list && new_list != stmt_list_ast) {
                                    // 更新 new_list 的 father 指针
                                    new_list->father = stmt_list_ast->father;
                                    
                                    if (stmt_list_ast->father) {
                                        replace_child_in_parent(stmt_list_ast->father, stmt_list_ast, new_list);
                                    } else {
                                        g_root_ast = new_list;
                                    }
                                    ast_modified = 1;
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }

        /* 如果AST被修改，跳过继续遍历当前节点的子节点，因为结构已经改变 */
        if (ast_modified) {
            // 重要：修改 AST 后，current 节点可能已经被替换或失效
            // 不要继续访问 current 的任何字段，直接跳过
            continue;
        }

        /* 继续遍历子节点 */
        // 在访问 current 的子节点之前，再次验证 current 是否仍然有效
        if (!current) {
            continue;
        }
        
        uint32_t count;
        zend_ast **children = ast_get_children(current, &count);
        if (!children) {
            continue;
        }
        
        for (uint32_t i = 0; i < count; i++) {
            if (children[i]) {
                // 验证子节点是否仍然有效
                if (children[i]->kind > 1000) {
                    continue;  // 跳过无效的节点类型
                }
                push(stack, children[i]);
            }
        }
    }

    free(stack->data);
    free(stack);
}


/* 辅助函数：从 JSON 字符串中提取字段值（简单实现，不依赖 JSON 库） */
static int extract_json_string_field(const char *json_str, const char *field_name, char *output, size_t output_size) {
    char search_pattern[256];
    snprintf(search_pattern, sizeof(search_pattern), "\"%s\"", field_name);
    
    const char *field_pos = strstr(json_str, search_pattern);
    if (!field_pos) {
        return 0;
    }
    
    /* 找到冒号 */
    const char *colon_pos = strchr(field_pos, ':');
    if (!colon_pos) {
        return 0;
    }
    
    /* 跳过空白字符 */
    colon_pos++;
    while (*colon_pos == ' ' || *colon_pos == '\t') {
        colon_pos++;
    }
    
    /* 提取字符串值（支持双引号字符串） */
    if (*colon_pos == '"') {
        colon_pos++;  // 跳过开头的引号
        size_t i = 0;
        while (*colon_pos != '"' && *colon_pos != '\0' && i < output_size - 1) {
            if (*colon_pos == '\\' && *(colon_pos + 1) == '"') {
                output[i++] = '"';
                colon_pos += 2;
            } else {
                output[i++] = *colon_pos++;
            }
        }
        output[i] = '\0';
        return 1;
    }
    
    /* 提取数字值（用于 line 字段） */
    if (*colon_pos >= '0' && *colon_pos <= '9') {
        size_t i = 0;
        while (*colon_pos >= '0' && *colon_pos <= '9' && i < output_size - 1) {
            output[i++] = *colon_pos++;
        }
        output[i] = '\0';
        return 1;
    }
    
    return 0;
}

/* 建议4：检查是否有断言失败或探针命中 */
static int has_assert_fail_or_probe_hit(void) {
    return dynamic_webshell_hit > 0;
}

/* 从动态日志中读取并更新调用图 */
static void load_dynamic_edges_and_update_graph(const char *log_path) {
    FILE *fp = fopen(log_path, "r");
    if (!fp) {
        /* 日志文件不存在是正常的（可能没有执行插桩后的脚本） */
        return;
    }
    
    char buf[4096];
    int line_count = 0;
    
    printf("正在读取动态日志: %s\n", log_path);
    
    while (fgets(buf, sizeof(buf), fp)) {
        line_count++;
        
        /* 移除换行符 */
        size_t len = strlen(buf);
        if (len > 0 && buf[len - 1] == '\n') {
            buf[len - 1] = '\0';
        }
        
        /* 跳过空行 */
        if (len <= 1) {
            continue;
        }
        
        /* 检查日志类型 - 新的调用图日志格式 */
        if (strstr(buf, "\"type\":\"dyn_call\"") || strstr(buf, "\"type\":\"dyn_call\"")) {
            /* 解析 file, line, caller, callee 字段 */
            char file[512] = {0};
            char line_str[64] = {0};
            char caller[256] = {0};
            char callee[256] = {0};
            
            extract_json_string_field(buf, "file", file, sizeof(file));
            extract_json_string_field(buf, "line", line_str, sizeof(line_str));
            extract_json_string_field(buf, "caller", caller, sizeof(caller));
            
            if (extract_json_string_field(buf, "callee", callee, sizeof(callee))) {
                if (strlen(callee) > 0 && strcmp(callee, "null") != 0) {
                    zend_string *func_name = zend_string_init(callee, strlen(callee), 0);
                    const char *caller_name = strlen(caller) > 0 ? caller : "__main__";
                    
                    printf("动态确认函数调用: %s -> %s (file: %s, line: %s)\n", 
                           caller_name, callee, strlen(file) > 0 ? file : "?", line_str);
                    
                    /* 将调用边添加到 call_graph_extra */
                    zend_string *caller_str = zend_string_init(caller_name, strlen(caller_name), 0);
                    
                    /* 检查 call_graph_extra 中是否已有该 caller */
                    zval *caller_val = zend_hash_find(&call_graph_extra, caller_str);
                    HashTable *callee_set = NULL;
                    
                    if (caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
                        callee_set = (HashTable *)Z_PTR_P(caller_val);
                    } else {
                        /* 创建新的 callee 集合 */
                        callee_set = (HashTable *)emalloc(sizeof(HashTable));
                        zend_hash_init(callee_set, 8, NULL, NULL, 1);
                        
                        zval new_caller_val;
                        ZVAL_PTR(&new_caller_val, callee_set);
                        zend_hash_add(&call_graph_extra, caller_str, &new_caller_val);
                    }
                    
                    /* 将 callee 添加到集合中 */
                    if (callee_set) {
                        zval callee_val;
                        ZVAL_LONG(&callee_val, 1);
                        zend_hash_add(callee_set, func_name, &callee_val);
                        printf("  添加动态调用边: %s -> %s\n", caller_name, callee);
                    }
                    
                    zend_string_release(caller_str);
                    
                    /* 检查是否是已知的危险函数 */
                    if (is_known_sink_function(func_name)) {
                        /* 将函数名添加到 sink_func_table（如果还没有） */
                        if (!zend_hash_exists(&sink_func_table, func_name)) {
                            zval func_val;
                            ZVAL_LONG(&func_val, sink_func_count);
                            sink_func_count++;
                            zend_hash_add(&sink_func_table, func_name, &func_val);
                            printf("已将危险函数 %s 添加到 sink_func_table\n", callee);
                        }
                    }
                    
                    zend_string_release(func_name);
                }
            }
        }
        else if (strstr(buf, "\"type\":\"eval\"") || strstr(buf, "\"type\":\"eval\"")) {
            /* 处理 EVAL 类型的日志 - 记录到 suspect_site_table */
            char line_str[64] = {0};
            if (extract_json_string_field(buf, "line", line_str, sizeof(line_str))) {
                printf("动态确认 EVAL 调用: line=%s\n", line_str);
                
                /* 构建 key: "file:line" */
                char site_key[512] = {0};
                if (current_filename) {
                    snprintf(site_key, sizeof(site_key), "%s:%s", 
                            ZSTR_VAL(current_filename), line_str);
                } else {
                    snprintf(site_key, sizeof(site_key), "?:%s", line_str);
                }
                
                zend_string *site_key_str = zend_string_init(site_key, strlen(site_key), 0);
                if (!zend_hash_exists(&suspect_site_table, site_key_str)) {
                    zval site_val;
                    ZVAL_STR(&site_val, zend_string_init("EVAL", 4, 0));
                    zend_hash_add(&suspect_site_table, site_key_str, &site_val);
                    printf("已将 EVAL 调用点添加到 suspect_site_table: %s\n", site_key);
                }
                zend_string_release(site_key_str);
            }
        }
        /* 建议2：解析 assert_fail / probe_hit 日志 */
        else if (strstr(buf, "\"type\":\"assert_fail\"") || strstr(buf, "\"type\":\"probe_hit\"")) {
            char line_str[64] = {0};
            char callee[256] = {0};
            extract_json_string_field(buf, "line", line_str, sizeof(line_str));
            extract_json_string_field(buf, "callee", callee, sizeof(callee));
            
            printf("检测到断言失败/探针命中: line=%s, callee=%s\n", line_str, callee);
            
            /* 构建 key: "file:line" */
            char site_key[512] = {0};
            if (current_filename) {
                snprintf(site_key, sizeof(site_key), "%s:%s",
                         ZSTR_VAL(current_filename), line_str);
            } else {
                snprintf(site_key, sizeof(site_key), "?:%s", line_str);
            }
            
            zend_string *site_key_str = zend_string_init(site_key, strlen(site_key), 0);
            if (!zend_hash_exists(&suspect_site_table, site_key_str)) {
                zval site_val;
                /* 可以把 callee 写进去，如 "ASSERT_FAIL(eval)" */
                char reason_buf[512] = {0};
                if (strlen(callee) > 0) {
                    snprintf(reason_buf, sizeof(reason_buf), "ASSERT_FAIL(%s)", callee);
                } else {
                    snprintf(reason_buf, sizeof(reason_buf), "ASSERT_FAIL");
                }
                zend_string *reason = zend_string_init(reason_buf, strlen(reason_buf), 0);
                ZVAL_STR(&site_val, reason);
                zend_hash_add(&suspect_site_table, site_key_str, &site_val);
                printf("已将断言失败点添加到 suspect_site_table: %s\n", site_key);
            }
            zend_string_release(site_key_str);
            
            /* ★★ 关键：这里直接打标记，后面判定用 */
            dynamic_webshell_hit++;
            printf("动态断言命中计数: %d\n", dynamic_webshell_hit);
        }
    }
    
    fclose(fp);
    
    if (line_count > 0) {
        printf("已处理 %d 条动态日志记录\n", line_count);
    } else {
        printf("动态日志文件为空或格式不正确\n");
    }
}

// 4. 导出AST并生成新脚本
void export_and_run(zend_ast *ast, const char *src_filename) {
    if (!ast) {
        printf("警告: AST为空，跳过导出\n");
        return;
    }
    
    // 导出AST为PHP代码，并在开头添加 __yz_runtime_probe 函数定义
    const char *probe_function = 
        "<?php\n"
        "// 动态探针函数：检查参数是否可疑\n"
        "function __yz_runtime_probe($type, $file, $line, $func, $callee = null, $arg = null) {\n"
        "    $log_file = '/tmp/yz_assert_log.jsonl';\n"
        "    $suspicious = false;\n"
        "    $reason = '';\n"
        "    \n"
        "    // 检查参数是否来自用户输入\n"
        "    $is_tainted = false;\n"
        "    if ($arg !== null) {\n"
        "        $arg_str = is_string($arg) ? $arg : (string)$arg;\n"
        "        // 简单检查：是否包含典型webshell特征\n"
        "        $webshell_patterns = ['eval', 'assert', 'system', 'exec', 'shell_exec', 'passthru', 'base64_decode', 'gzinflate', 'str_rot13'];\n"
        "        foreach ($webshell_patterns as $pattern) {\n"
        "            if (stripos($arg_str, $pattern) !== false) {\n"
        "                $suspicious = true;\n"
        "                $reason = 'tainted user payload with code: ' . substr($arg_str, 0, 100);\n"
        "                break;\n"
        "            }\n"
        "        }\n"
        "        // 检查是否来自超全局变量\n"
        "        foreach (['_GET', '_POST', '_REQUEST', '_COOKIE', '_FILES'] as $super) {\n"
        "            if (isset($GLOBALS[$super]) && is_array($GLOBALS[$super])) {\n"
        "                foreach ($GLOBALS[$super] as $val) {\n"
        "                    if (is_string($val) && strpos($arg_str, $val) !== false) {\n"
        "                        $is_tainted = true;\n"
        "                        break 2;\n"
        "                    }\n"
        "                }\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "    \n"
        "    // 检查函数名是否危险\n"
        "    if ($callee !== null) {\n"
        "        $callee_str = is_string($callee) ? $callee : (string)$callee;\n"
        "        $dangerous_funcs = ['eval', 'assert', 'exec', 'shell_exec', 'system', 'preg_replace', 'file_put_contents', 'fwrite', 'fputs', 'call_user_func_array', 'array_map', 'copy', 'call_user_func'];\n"
        "        if (in_array(strtolower($callee_str), $dangerous_funcs)) {\n"
        "            $suspicious = true;\n"
        "            if (empty($reason)) {\n"
        "                $reason = 'dangerous function: ' . $callee_str;\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "    \n"
        "    // 如果可疑，记录日志并返回false（触发assert失败）\n"
        "    if ($suspicious || ($is_tainted && $arg !== null)) {\n"
        "        $log_entry = json_encode([\n"
        "            'type' => 'assert_fail',\n"
        "            'file' => $file,\n"
        "            'line' => $line,\n"
        "            'caller' => $func ?: '__main__',\n"
        "            'callee' => $callee ? (is_string($callee) ? $callee : (string)$callee) : null,\n"
        "            'reason' => $reason ?: 'suspicious parameter detected',\n"
        "            'score' => 0.9\n"
        "        ]) . \"\\n\";\n"
        "        file_put_contents($log_file, $log_entry, FILE_APPEND | LOCK_EX);\n"
        "        return false;  // 触发assert失败，终止执行\n"
        "    }\n"
        "    \n"
        "    // 安全，返回true\n"
        "    return true;\n"
        "}\n"
        "\n";
    
    const char *suffix = "\n";
    zend_string *generated_code = zend_ast_export(probe_function, ast, suffix);
    
    if (!generated_code) {
        printf("警告: AST导出失败，跳过文件生成\n");
        return;
    }

    // 只取文件名部分
    const char *base = strrchr(src_filename, '/');
    base = base ? base + 1 : src_filename;

    // 拼接新文件名
    const char *dir = "/home/yz/Desktop";
    char filename[512];
    snprintf(filename, sizeof(filename), "%s/%s_test.php", dir, base);

    // 写入临时文件
    FILE *fp = fopen(filename, "w");
    if (!fp) {
        printf("警告: 无法写入文件 %s，跳过导出\n", filename);
        zend_string_release(generated_code);
        return;
    }
    fwrite(ZSTR_VAL(generated_code), ZSTR_LEN(generated_code), 1, fp);
    fclose(fp);

    // 建议3：在沙箱环境中执行生成的脚本（用于动态补充调用图）
    printf("正在沙箱执行插桩后的脚本以收集动态调用信息...\n");
    char command[1024];
    /* 添加沙箱限制：
     * - disable_functions: 禁用危险系统调用
     * - max_execution_time: 限制执行时间（3秒）
     * - memory_limit: 限制内存（32M）
     * - 重定向输出到日志文件
     */
    snprintf(command, sizeof(command),
             "php -d disable_functions=system,exec,shell_exec,passthru,popen,proc_open,"
             "pcntl_exec,proc_open,proc_get_status,proc_nice,proc_terminate "
             "-d max_execution_time=3 "
             "-d memory_limit=32M "
             "%s > /tmp/yz_php_stdout.log 2>&1",
             filename);
    int ret = system(command);
    if (ret != 0) {
        printf("警告: 脚本执行返回非零退出码 %d（可能是防御逻辑触发了 exit 或超时）\n", ret);
    } else {
        printf("脚本执行完成\n");
    }

    // 清理资源
    zend_string_release(generated_code);
}

// 全局变量，用于在段错误处理中记录文件信息
static size_t g_file_size_on_segfault = 0;
static size_t g_file_lines_on_segfault = 0;
static const char* g_file_name_on_segfault = NULL;

// 段错误处理函数
static void segfault_handler(int sig) {
    printf("\n错误: 程序在处理文件时发生段错误（Segmentation Fault）\n");
    printf("可能原因:\n");
    printf("  1. 文件包含超长的字符串字面量（如超长base64编码）\n");
    printf("  2. 词法分析器缓冲区溢出\n");
    printf("  3. 文件格式异常或损坏\n");
    if (g_file_size_on_segfault > 0) {
        printf("文件信息: 大小 %zu 字节", g_file_size_on_segfault);
        if (g_file_lines_on_segfault > 0) {
            printf("，约 %zu 行", g_file_lines_on_segfault);
        }
        printf("\n");
    }
    if (g_file_name_on_segfault) {
        printf("文件路径: %s\n", g_file_name_on_segfault);
    }
    printf("\n========================================\n");
    printf("检测结果: 无法处理（词法分析器限制）\n");
    printf("========================================\n");
    if (g_file_name_on_segfault) {
        printf("文件: %s\n", g_file_name_on_segfault);
    }
    printf("原因: 词法分析器在处理文件时崩溃（段错误）\n");
    printf("建议: 检查文件内容，或使用其他检测工具\n");
    exit(1);
}
  
int main(int argc, char *argv[]) {
  int a = 0;
  int i;

  // 在程序开始时就设置信号处理器，捕获段错误
  signal(SIGSEGV, segfault_handler);

  // 检查命令行参数
  if (argc < 2) {
    printf("Usage: %s <php_file>\n", argv[0]);
    printf("检测PHP文件是否为Webshell\n");
    return 1;
  }

  // 记录文件名到全局变量（用于段错误处理）
  g_file_name_on_segfault = argv[1];

  // 检查文件是否存在并获取文件大小
  FILE *test_file = fopen(argv[1], "rb");
  if (!test_file) {
    printf("错误: 无法打开文件 '%s'\n", argv[1]);
    return 1;
  }
  
  // 获取文件大小
  fseek(test_file, 0, SEEK_END);
  long file_size_check = ftell(test_file);
  fclose(test_file);
  
  // 提前检查文件大小，对于超大文件直接拒绝
  if (file_size_check > 5 * 1024 * 1024) {  // 5MB
    printf("========================================\n");
    printf("PHP WebShell 检测工具\n");
    printf("========================================\n");
    printf("正在分析文件: %s\n", argv[1]);
    printf("----------------------------------------\n");
    printf("错误: 文件过大（%ld 字节，超过 5MB），无法处理\n", file_size_check);
    printf("可能原因: 文件过大，超出词法分析器处理能力\n");
    printf("\n========================================\n");
    printf("检测结果: 无法处理（文件过大）\n");
    printf("========================================\n");
    printf("文件: %s\n", argv[1]);
    printf("原因: 文件大小超出处理限制（5MB）\n");
    printf("建议: 使用其他检测工具或预处理文件\n");
    return 1;
  }

  printf("========================================\n");
  printf("PHP WebShell 检测工具\n");
  printf("========================================\n");
  printf("正在分析文件: %s\n", argv[1]);
  printf("----------------------------------------\n");

        start_memory_manager();
        zend_interned_strings_init();

        zend_ast *ast;
        zend_arena *ast_arena;

/*
        FILE *file = fopen(argv[1], "r");

        fseek(file, 0, SEEK_END);
        int size = ftell(file);
        fseek(file, 0, SEEK_SET);
        char *source = (char *)malloc(sizeof(char) * size + 1);
        fread(source, 1, size, file);
        fclose(file);
        source[size] = '\0';
        printf("file name is %s\n", argv[1]);
        printf("file size is %d\n", size);
        //printf("code is %s\n", source);

        zend_string *filename = zend_string_init(argv[1], strlen(argv[1]),0);
        zend_string *code = zend_string_init(source, strlen(source) - 1, 0);
        printf("code is %s\n", code->val);

*/

    FILE *file = fopen(argv[1], "rb");
    struct stat st;
    fstat(fileno(file), &st);
    size_t file_size = st.st_size;
    char *source = NULL;
    size_t bytes_read = 0;
    if (file_size > 0) {
        source = malloc(file_size + 1);
        bytes_read = fread(source, 1, file_size, file);
    } else {
        source = malloc(1);
        if (source) *source = '\0';
        bytes_read = 0;
    }
    fclose(file);
    source[bytes_read] = '\0';
    
    // 在释放 source 之前，先检查文件内容是否是非 PHP 文件或可疑脚本
    bool is_perl_script = false;
    bool is_suspicious_script = false;
    int keyword_count = 0;
    
    // 1. 检查是否有 Perl shebang
    if (bytes_read >= 14 && memcmp(source, "#!/usr/bin/perl", 14) == 0) {
        is_perl_script = true;
        is_suspicious_script = true;
    } else if (bytes_read >= 13 && memcmp(source, "#!/usr/bin/env", 13) == 0) {
        // 检查是否是 perl
        if (bytes_read >= 20 && memcmp(source, "#!/usr/bin/env perl", 20) == 0) {
            is_perl_script = true;
            is_suspicious_script = true;
        }
    }
    
    // 2. 检查文件内容中是否包含可疑关键词（即使没有 shebang）
    if (!is_perl_script && bytes_read > 0) {
        const char *suspicious_keywords[] = {
            "backdoor", "Backdoor", "BACKDOOR",
            "shell", "Shell", "SHELL",
            "connect", "Connect", "CONNECT",
            "socket", "Socket", "SOCKET",
            "bind", "Bind", "BIND",
            "reverse", "Reverse", "REVERSE",
            "exploit", "Exploit", "EXPLOIT"
        };
        size_t num_keywords = sizeof(suspicious_keywords) / sizeof(suspicious_keywords[0]);
        for (size_t i = 0; i < num_keywords; i++) {
            if (strstr(source, suspicious_keywords[i]) != NULL) {
                keyword_count++;
            }
        }
        // 如果包含多个可疑关键词，可能是恶意脚本
        if (keyword_count >= 2) {
            is_suspicious_script = true;
        }
    }
    
    zend_string *filename = zend_string_init(argv[1], strlen(argv[1]),0);
    zend_string *code = zend_string_init(source, bytes_read, 0);
    current_filename = zend_string_copy(filename);
    free(source);

        zend_hash_init(&tainted_table, 64, NULL, NULL, 1);
        zend_hash_init(&local_tainted_table, 64, NULL, NULL, 1);

        zend_hash_init(&var_source_table, 64, NULL, NULL, 1);
        zend_hash_init(&func_source_table, 64, NULL, NULL, 1);

        zend_hash_init(&sink_table, 64, NULL, NULL, 1);
        zend_hash_init(&sink_var_table, 64, NULL, NULL, 1);
        zend_hash_init(&var_value_table, 64, NULL, ZVAL_PTR_DTOR, 0);
        zend_hash_init(&sink_func_table, 64, NULL, NULL, 1);
        zend_hash_init(&local_sink_table, 64, NULL, NULL, 1);

        zend_hash_init(&webshell_table, 64, NULL, NULL, 1);
        //suspect_site_table 初始化
        zend_hash_init(&suspect_site_table, 8, NULL, ZVAL_PTR_DTOR, 0);
        //call_graph_extra 初始化（动态补充的调用图边）
        zend_hash_init(&call_graph_extra, 8, NULL, ZVAL_PTR_DTOR, 0);
        //call_graph_static 初始化（静态调用图）
        zend_hash_init(&call_graph_static, 8, NULL, ZVAL_PTR_DTOR, 0);

        int var_source_num = 6;
        char *var_source[6] = {"_POST", "_GET", "_REQUEST", "_COOKIE", "_FILES", "_SERVER"};

        for (i = 0;i < var_source_num;i++) {
          zend_string *string_var = zend_string_init(var_source[i], strlen(var_source[i]), 0);
          zval index_val;
          ZVAL_LONG(&index_val, i+1);
          zend_hash_add(&var_source_table, string_var, &index_val);
        }

        int func_source_num = 5;
        char *func_source[5] = {"file_get_contents", "fopen", "fread", "getallheaders", "getenv"};

        for (i = 0;i < func_source_num;i++) {
          zend_string *string_var = zend_string_init(func_source[i], strlen(func_source[i]), 0);
          zval index_val;
          ZVAL_LONG(&index_val, i+1);
          zend_hash_add(&func_source_table, string_var, &index_val);
        }

        func_source_count = func_source_num;

        int sink_num = 36;
        char *sink_name[36] = {"eval", "assert", "exec", "shell_exec", "system", "passthru", "preg_replace", "file_put_contents", "fopen", "fwrite", "fputs", "move_uploaded_file", "call_user_func_array", "array_map", "copy", "call_user_func", "array_filter", "array_walk", "array_walk_recursive", "register_tick_function", "eval_r", "create_function", "uasort", "array_udiff_assoc", "forward_static_call_array", "uksort", "array_reduce", "register_shutdown_function", "filter_var", "filter_var_array", "preg_replace_callback", "mb_ereg_replace_callback", "popen", "yaml_parse", "gzinflate", "base64_decode"};

        for (i = 0;i < sink_num;i++) {
          zend_string *string_var = zend_string_init(sink_name[i], strlen(sink_name[i]), 0);
          zval index_val;
          ZVAL_LONG(&index_val, i+1);
          zend_hash_add(&sink_table, string_var, &index_val);
        }

        sink_count = sink_num;

        printf("正在编译PHP代码到AST...\n");
        
        // 更新全局变量（用于段错误处理）
        g_file_size_on_segfault = file_size;
        g_file_lines_on_segfault = 0;
        
        // 检查文件大小和行数，避免词法分析器处理超大文件时崩溃
        // 对于大文件，简化检查以避免在检查过程中崩溃
        size_t line_count_estimate = 0;
        size_t check_limit = bytes_read;
        
        // 对于大文件（>500KB），只检查前100KB来估算行数，避免全文件扫描导致崩溃
        if (file_size > 500 * 1024) {
            check_limit = 100 * 1024;  // 只检查前100KB
            printf("警告: 文件较大 (%zu 字节)，将进行简化检查\n", file_size);
        }
        
        for (size_t i = 0; i < check_limit; i++) {
            if (source[i] == '\n') {
                line_count_estimate++;
            }
        }
        
        // 如果只检查了部分文件，估算总行数
        if (check_limit < bytes_read) {
            line_count_estimate = (line_count_estimate * bytes_read) / check_limit;
        }
        
        g_file_lines_on_segfault = line_count_estimate;
        
        if (file_size > 1 * 1024 * 1024) {  // 1MB
            printf("警告: 文件较大 (%zu 字节，约 %zu 行)，词法分析可能需要较长时间\n", 
                   file_size, line_count_estimate);
        }
        
        // 检查行数，如果行数过多也可能导致问题
        if (line_count_estimate > 10000) {
            printf("警告: 文件行数较多（约 %zu 行），可能导致词法分析器处理困难\n", line_count_estimate);
            // 对于超大文件，直接拒绝处理
            if (line_count_estimate > 20000 || file_size > 2 * 1024 * 1024) {
                printf("\n========================================\n");
                printf("检测结果: 无法处理（文件过大）\n");
                printf("========================================\n");
                printf("文件: %s\n", ZSTR_VAL(filename));
                printf("原因: 文件过大（%zu 字节，约 %zu 行），超出词法分析器处理能力\n", 
                       file_size, line_count_estimate);
                printf("建议: 使用其他检测工具或预处理文件\n");
                zend_string_release(code);
                zend_string_release(filename);
                return 1;
            }
        }
        
        // 检查是否有超长的字符串字面量（可能导致词法分析器崩溃）
        // 对于大文件，简化字符串检查，只检查前100KB
        size_t max_string_length = 0;
        size_t current_string_length = 0;
        int in_string = 0;
        int in_single_quote = 0;
        int in_double_quote = 0;
        int line_count = 0;
        int max_line_count = 0;
        char quote_char = 0;
        int has_variable_interpolation = 0;
        
        // 限制字符串检查的范围，避免大文件导致崩溃
        size_t string_check_limit = (file_size > 500 * 1024) ? 100 * 1024 : bytes_read;
        
        for (size_t i = 0; i < string_check_limit; i++) {
            // 处理换行符
            if (source[i] == '\n') {
                if (in_string) {
                    line_count++;
                }
            }
            
            if (!in_string) {
                // 检查是否是字符串开始
                if (source[i] == '"') {
                    in_string = 1;
                    in_double_quote = 1;
                    quote_char = '"';
                    current_string_length = 1;
                    line_count = 1;
                    has_variable_interpolation = 0;
                } else if (source[i] == '\'') {
                    in_string = 1;
                    in_single_quote = 1;
                    quote_char = '\'';
                    current_string_length = 1;
                    line_count = 1;
                    has_variable_interpolation = 0;
                }
            } else {
                current_string_length++;
                
                // 检查变量插值（双引号字符串中）
                if (in_double_quote && i > 0 && source[i-1] != '\\') {
                    if (source[i] == '$' || (source[i] == '.' && i > 0 && source[i-1] == '"')) {
                        has_variable_interpolation = 1;
                    }
                }
                
                // 检查字符串结束
                if (source[i] == quote_char) {
                    // 检查是否是转义的引号（需要检查前一个字符是否是反斜杠）
                    int is_escaped = 0;
                    if (i > 0 && source[i-1] == '\\') {
                        // 检查是否是双重转义（\\"）
                        if (i > 1 && source[i-2] == '\\') {
                            is_escaped = 0;  // \\" 表示转义的反斜杠+引号，引号未转义
                        } else {
                            is_escaped = 1;  // \" 表示转义的引号
                        }
                    }
                    
                    if (!is_escaped) {
                        // 对于双引号，检查是否是变量插值的结束（如 ".$var."）
                        // 格式：字符串结束引号后跟点号，然后是变量或另一个字符串
                        if (quote_char == '"' && i + 1 < bytes_read) {
                            // 跳过空白字符
                            size_t j = i + 1;
                            while (j < bytes_read && (source[j] == ' ' || source[j] == '\t' || source[j] == '\n' || source[j] == '\r')) {
                                j++;
                            }
                            
                            // 检查 ".$var." 或 "string".$var."string" 模式
                            if (j < bytes_read && (source[j] == '.' || source[j] == '$')) {
                                // 可能是变量插值，继续处理字符串（不结束字符串）
                                continue;
                            }
                        }
                        
                        // 字符串真正结束
                        if (current_string_length > max_string_length) {
                            max_string_length = current_string_length;
                            max_line_count = line_count;
                        }
                        
                        // 检查是否是有问题的字符串
                        if (current_string_length > 5000 || line_count > 10) {
                            printf("警告: 检测到复杂字符串字面量（长度: %zu 字节，跨 %d 行）\n", 
                                   current_string_length, line_count);
                            if (has_variable_interpolation) {
                                printf("  包含变量插值，可能导致词法分析器处理困难\n");
                            }
                        }
                        
                        in_string = 0;
                        in_single_quote = 0;
                        in_double_quote = 0;
                        current_string_length = 0;
                        line_count = 0;
                        has_variable_interpolation = 0;
                    }
                }
            }
        }
        
        // 如果字符串没有正确结束，也可能导致问题
        // 但是，对于混淆代码，可能包含特殊语法，导致检测误判
        // 所以，即使检测到未闭合字符串，也尝试继续解析（只输出警告）
        if (in_string) {
            // 如果字符串长度很短（<100字节），可能是检测误判，只输出警告
            if (current_string_length < 100) {
                printf("警告: 检测到可能未闭合的字符串字面量（长度: %zu 字节），可能是检测误判，将尝试继续解析\n", current_string_length);
            } else {
                printf("警告: 检测到未闭合的字符串字面量（可能跨多行，长度: %zu 字节）\n", current_string_length);
                printf("可能原因: 多行字符串或字符串中包含复杂内容\n");
                printf("将尝试继续解析，但可能发生段错误\n");
            }
            // 不直接退出，尝试继续解析
        }
        
        // 检查是否包含可能导致段错误的字符串
        // 改进：放宽限制条件，并先进行源代码模式匹配检测
        int should_skip = 0;
        if (max_string_length > 200000) {  // 放宽到 200KB
            printf("错误: 检测到超长字符串字面量（%zu 字节，跨 %d 行），可能导致词法分析器崩溃\n", 
                   max_string_length, max_line_count);
            printf("可能原因: 文件包含超长的base64编码或其他编码字符串\n");
            printf("此类文件已知会导致段错误，跳过词法分析以避免崩溃\n");
            should_skip = 1;
        } else if (max_string_length > 10000 && max_line_count > 20) {
            // 放宽限制：>10KB 且跨 >20 行（原来是 >5KB 且跨 >10 行）
            printf("错误: 检测到复杂的多行字符串字面量（长度: %zu 字节，跨 %d 行）\n", 
                   max_string_length, max_line_count);
            printf("可能原因: 字符串包含HTML/CSS/JavaScript代码或变量插值\n");
            printf("此类文件在词法分析阶段已知会导致段错误，跳过词法分析以避免崩溃\n");
            printf("建议: 请使用其他检测工具或预处理文件\n");
            should_skip = 1;
        } else if (max_string_length > 20000 && max_line_count > 10) {
            printf("警告: 检测到较长的多行字符串字面量（%zu 字节，跨 %d 行）\n", 
                   max_string_length, max_line_count);
            printf("可能原因: 字符串包含HTML/CSS/JavaScript代码或变量插值\n");
            printf("建议: 此类文件可能导致词法分析器处理困难，可能发生段错误\n");
        }
        
        // 信号处理器已在程序开始时设置，这里只需要更新文件信息
        g_file_size_on_segfault = file_size;
        g_file_lines_on_segfault = line_count_estimate;
        g_file_name_on_segfault = ZSTR_VAL(filename);
        
        // 启用短标签支持（<? 和 <?=）
        CG(short_tags) = 1;
        
        // 改进：在解析之前，先检查源代码中是否包含危险的文件操作函数
        // 这样可以确保即使 AST 解析失败，也能检测到基本的 webshell 特征
        const char *dangerous_patterns[] = {
          "fopen", "fwrite", "file_put_contents", "fputs",
          "base64_decode", "gzinflate", "eval", "assert",
          "move_uploaded_file", "exec", "system", "shell_exec", "passthru"
        };
        int pattern_count = sizeof(dangerous_patterns) / sizeof(dangerous_patterns[0]);
        int dangerous_count = 0;
        for (int i = 0; i < pattern_count; i++) {
          if (strstr(ZSTR_VAL(code), dangerous_patterns[i]) != NULL) {
            dangerous_count++;
            printf("DEBUG: 在源代码中发现危险函数: %s\n", dangerous_patterns[i]);
          }
        }
        if (dangerous_count >= 2) {
          printf("DEBUG: 警告：源代码中包含 %d 个危险函数/操作，可能是 webshell\n", dangerous_count);
        }
        
        // 检查图片马特征：文件开头是图片文件头（GIF89a, PNG, JPEG等），后面跟着PHP代码
        bool is_image_webshell = false;
        if (bytes_read >= 6) {
          // 检查是否是 GIF 文件头（GIF89a, GIF87a, GIF89a1等）
          if ((memcmp(source, "GIF89a", 6) == 0) || 
              (memcmp(source, "GIF87a", 6) == 0) ||
              (bytes_read >= 7 && memcmp(source, "GIF89a1", 7) == 0)) {
            // 检查后面是否包含 PHP 代码特征
            if (strstr(source, "move_uploaded_file") != NULL ||
                strstr(source, "$_FILES") != NULL ||
                strstr(source, "$_REQUEST") != NULL ||
                strstr(source, "$_SERVER") != NULL ||
                strstr(source, "$_POST") != NULL ||
                strstr(source, "$_GET") != NULL ||
                strstr(source, "eval") != NULL ||
                strstr(source, "assert") != NULL ||
                strstr(source, "exec") != NULL ||
                strstr(source, "system") != NULL) {
              is_image_webshell = true;
              printf("DEBUG: 检测到图片马特征：GIF 文件头后面跟着 PHP webshell 代码\n");
            }
          }
          // 检查是否是 PNG 文件头
          if (bytes_read >= 8 && memcmp(source, "\x89PNG\r\n\x1a\n", 8) == 0) {
            if (strstr(source, "move_uploaded_file") != NULL ||
                strstr(source, "$_FILES") != NULL ||
                strstr(source, "$_REQUEST") != NULL ||
                strstr(source, "eval") != NULL ||
                strstr(source, "assert") != NULL) {
              is_image_webshell = true;
              printf("DEBUG: 检测到图片马特征：PNG 文件头后面跟着 PHP webshell 代码\n");
            }
          }
          // 检查是否是 JPEG 文件头
          if (bytes_read >= 3 && memcmp(source, "\xff\xd8\xff", 3) == 0) {
            if (strstr(source, "move_uploaded_file") != NULL ||
                strstr(source, "$_FILES") != NULL ||
                strstr(source, "$_REQUEST") != NULL ||
                strstr(source, "eval") != NULL ||
                strstr(source, "assert") != NULL) {
              is_image_webshell = true;
              printf("DEBUG: 检测到图片马特征：JPEG 文件头后面跟着 PHP webshell 代码\n");
            }
          }
        }
        
        // 检查文件上传相关的webshell特征
        bool has_upload_webshell = false;
        if (strstr(ZSTR_VAL(code), "move_uploaded_file") != NULL &&
            (strstr(ZSTR_VAL(code), "$_FILES") != NULL ||
             strstr(ZSTR_VAL(code), "$_REQUEST") != NULL ||
             strstr(ZSTR_VAL(code), "$_POST") != NULL ||
             strstr(ZSTR_VAL(code), "$_GET") != NULL)) {
          has_upload_webshell = true;
          printf("DEBUG: 检测到文件上传webshell特征：move_uploaded_file 与超全局变量组合\n");
        }
        
        // 检查密码验证相关的webshell特征（md5 + $_REQUEST）
        bool has_password_auth = false;
        if (strstr(ZSTR_VAL(code), "md5") != NULL &&
            (strstr(ZSTR_VAL(code), "$_REQUEST") != NULL ||
             strstr(ZSTR_VAL(code), "$_POST") != NULL ||
             strstr(ZSTR_VAL(code), "$_GET") != NULL)) {
          has_password_auth = true;
          printf("DEBUG: 检测到密码验证webshell特征：md5 与超全局变量组合\n");
        }
        
        // 检查WSO webshell特征和其他webshell特征字符串
        const char *webshell_signatures[] = {
          "wso_version", "WSO_VERSION", "wso_",
          "backdoor", "Backdoor", "BACKDOOR",
          "webshell", "WebShell", "WEBSHELL",
          "c99shell", "C99Shell", "C99SHELL",
          "r57shell", "R57Shell", "R57SHELL",
          "phpspy", "PHPSpy", "PHPSPY",
          "c99", "r57", "wso",
          "zcg:function", "XSLTProcessor", "registerPHPFunctions"
        };
        int signature_count = sizeof(webshell_signatures) / sizeof(webshell_signatures[0]);
        int signature_match_count = 0;
        for (int i = 0; i < signature_count; i++) {
          if (strstr(ZSTR_VAL(code), webshell_signatures[i]) != NULL) {
            signature_match_count++;
            printf("DEBUG: 在源代码中发现webshell特征: %s\n", webshell_signatures[i]);
          }
        }
        
        // 检查序列化数据中的webshell特征（如 "s:4:\"pass\"" 或 "s:8:\"backdoor\""）
        bool has_serialized_webshell = false;
        if (strstr(ZSTR_VAL(code), "s:4:\"pass\"") != NULL || 
            strstr(ZSTR_VAL(code), "s:8:\"backdoor\"") != NULL ||
            strstr(ZSTR_VAL(code), "s:11:\"wso_version\"") != NULL ||
            strstr(ZSTR_VAL(code), "\"pass\"") != NULL ||
            strstr(ZSTR_VAL(code), "\"backdoor\"") != NULL ||
            strstr(ZSTR_VAL(code), "\"wso_version\"") != NULL) {
          has_serialized_webshell = true;
          printf("DEBUG: 在源代码中发现序列化数据中的webshell特征\n");
        }
        
        // 检查XSLT相关的webshell特征
        bool has_xslt_webshell = false;
        if ((strstr(ZSTR_VAL(code), "zcg:function") != NULL && 
             (strstr(ZSTR_VAL(code), "assert") != NULL || strstr(ZSTR_VAL(code), "eval") != NULL)) ||
            (strstr(ZSTR_VAL(code), "XSLTProcessor") != NULL && 
             strstr(ZSTR_VAL(code), "registerPHPFunctions") != NULL) ||
            (strstr(ZSTR_VAL(code), "assert(") != NULL && strstr(ZSTR_VAL(code), "$_POST") != NULL) ||
            (strstr(ZSTR_VAL(code), "assert(") != NULL && strstr(ZSTR_VAL(code), "$_GET") != NULL) ||
            (strstr(ZSTR_VAL(code), "assert(") != NULL && strstr(ZSTR_VAL(code), "$_REQUEST") != NULL)) {
          has_xslt_webshell = true;
          printf("DEBUG: 在源代码中发现XSLT webshell特征\n");
        }
        
        // 检查字符串中包含危险函数调用模式（如 system($_GET[...])）
        bool has_string_dangerous_call = false;
        if ((strstr(ZSTR_VAL(code), "system(") != NULL && (strstr(ZSTR_VAL(code), "$_GET") != NULL || strstr(ZSTR_VAL(code), "$_POST") != NULL || strstr(ZSTR_VAL(code), "$_REQUEST") != NULL)) ||
            (strstr(ZSTR_VAL(code), "exec(") != NULL && (strstr(ZSTR_VAL(code), "$_GET") != NULL || strstr(ZSTR_VAL(code), "$_POST") != NULL || strstr(ZSTR_VAL(code), "$_REQUEST") != NULL)) ||
            (strstr(ZSTR_VAL(code), "shell_exec(") != NULL && (strstr(ZSTR_VAL(code), "$_GET") != NULL || strstr(ZSTR_VAL(code), "$_POST") != NULL || strstr(ZSTR_VAL(code), "$_REQUEST") != NULL)) ||
            (strstr(ZSTR_VAL(code), "passthru(") != NULL && (strstr(ZSTR_VAL(code), "$_GET") != NULL || strstr(ZSTR_VAL(code), "$_POST") != NULL || strstr(ZSTR_VAL(code), "$_REQUEST") != NULL))) {
          has_string_dangerous_call = true;
          printf("DEBUG: 在源代码中发现字符串中包含危险函数调用模式（如 system(\$_GET[...])）\n");
        }
        
        // 检查SQL注入特征（INTO OUTFILE）
        bool has_sql_injection = false;
        if (strstr(ZSTR_VAL(code), "INTO OUTFILE") != NULL || strstr(ZSTR_VAL(code), "into outfile") != NULL ||
            strstr(ZSTR_VAL(code), "INTO outfile") != NULL || strstr(ZSTR_VAL(code), "into OUTFILE") != NULL) {
          // 如果包含 INTO OUTFILE 且包含危险函数或超全局变量，标记为可疑
          if (strstr(ZSTR_VAL(code), "system") != NULL || strstr(ZSTR_VAL(code), "exec") != NULL ||
              strstr(ZSTR_VAL(code), "eval") != NULL || strstr(ZSTR_VAL(code), "assert") != NULL ||
              strstr(ZSTR_VAL(code), "$_GET") != NULL || strstr(ZSTR_VAL(code), "$_POST") != NULL ||
              strstr(ZSTR_VAL(code), "$_REQUEST") != NULL) {
            has_sql_injection = true;
            printf("DEBUG: 在源代码中发现SQL注入特征（INTO OUTFILE）且包含危险函数或超全局变量\n");
          } else {
            // 即使不包含危险函数，INTO OUTFILE 本身也很可疑（SQL注入写入文件）
            has_sql_injection = true;
            printf("DEBUG: 在源代码中发现SQL注入特征（INTO OUTFILE）\n");
          }
        }
        
        // 检查 Closure::fromCallable 调用（用于动态调用函数）
        bool has_closure_fromcallable = false;
        if (strstr(ZSTR_VAL(code), "Closure::fromCallable") != NULL ||
            strstr(ZSTR_VAL(code), "fromCallable") != NULL) {
          has_closure_fromcallable = true;
          printf("DEBUG: 在源代码中发现 Closure::fromCallable 调用（用于动态调用函数）\n");
        }
        
        // 检查 __invoke 方法调用（用于动态调用函数）
        bool has_invoke_method = false;
        if (strstr(ZSTR_VAL(code), "__invoke") != NULL) {
          has_invoke_method = true;
          printf("DEBUG: 在源代码中发现 __invoke 方法调用（用于动态调用函数）\n");
        }
        
        // 检查 array_diff + join 组合（用于拼接函数名）
        bool has_array_diff_join = false;
        if (strstr(ZSTR_VAL(code), "array_diff") != NULL && strstr(ZSTR_VAL(code), "join") != NULL) {
          has_array_diff_join = true;
          printf("DEBUG: 在源代码中发现 array_diff + join 组合（可能用于拼接函数名）\n");
        }
        
        // 检查 unserialize 调用（可能用于触发反序列化漏洞）
        bool has_unserialize = false;
        if (strstr(ZSTR_VAL(code), "unserialize") != NULL) {
          has_unserialize = true;
          printf("DEBUG: 在源代码中发现 unserialize 调用（可能用于触发反序列化漏洞）\n");
        }
        
        // 改进：如果检测到文件操作函数和解码函数的组合，直接标记为 webshell
        bool has_file_op = (strstr(ZSTR_VAL(code), "fopen") != NULL || 
                            strstr(ZSTR_VAL(code), "fwrite") != NULL ||
                            strstr(ZSTR_VAL(code), "file_put_contents") != NULL ||
                            strstr(ZSTR_VAL(code), "move_uploaded_file") != NULL);
        bool has_decode = (strstr(ZSTR_VAL(code), "base64_decode") != NULL ||
                           strstr(ZSTR_VAL(code), "gzinflate") != NULL);
        printf("DEBUG: 源代码模式匹配检查: has_file_op=%d, has_decode=%d, dangerous_count=%d, signature_match_count=%d, has_serialized_webshell=%d, has_xslt_webshell=%d, is_image_webshell=%d, has_upload_webshell=%d, has_password_auth=%d, has_string_dangerous_call=%d, has_sql_injection=%d, has_closure_fromcallable=%d, has_invoke_method=%d, has_array_diff_join=%d, has_unserialize=%d\n", 
               has_file_op, has_decode, dangerous_count, signature_match_count, has_serialized_webshell, has_xslt_webshell, is_image_webshell, has_upload_webshell, has_password_auth, has_string_dangerous_call, has_sql_injection, has_closure_fromcallable, has_invoke_method, has_array_diff_join, has_unserialize);
        
        // 如果检测到webshell特征字符串，直接标记为webshell
        if (signature_match_count > 0 || has_serialized_webshell || has_xslt_webshell || 
            is_image_webshell || has_upload_webshell || has_password_auth ||
            has_string_dangerous_call || has_sql_injection ||
            has_closure_fromcallable || has_invoke_method || has_array_diff_join || has_unserialize) {
          printf("DEBUG: 源代码模式匹配：发现webshell特征字符串，直接标记为 webshell\n");
          webshell = 1;  // 直接标记为 webshell
          printf("DEBUG: 已设置 webshell = 1\n");
        } else if (has_file_op && has_decode) {
          printf("DEBUG: 源代码模式匹配：发现文件操作函数和解码函数组合，直接标记为 webshell\n");
          webshell = 1;  // 直接标记为 webshell
          printf("DEBUG: 已设置 webshell = 1\n");
        } else if (dangerous_count >= 2) {
          // 如果检测到 2 个或更多危险函数，也标记为可疑（降低阈值从3到2）
          printf("DEBUG: 源代码模式匹配：检测到 %d 个危险函数，标记为可疑\n", dangerous_count);
          webshell = 1;  // 标记为可疑
          printf("DEBUG: 已设置 webshell = 1\n");
        } else if (has_file_op) {
          // 如果检测到文件操作函数，且包含超全局变量，也标记为可疑
          if (strstr(ZSTR_VAL(code), "$_FILES") != NULL ||
              strstr(ZSTR_VAL(code), "$_REQUEST") != NULL ||
              strstr(ZSTR_VAL(code), "$_POST") != NULL ||
              strstr(ZSTR_VAL(code), "$_GET") != NULL ||
              strstr(ZSTR_VAL(code), "$_SERVER") != NULL) {
            printf("DEBUG: 源代码模式匹配：发现文件操作函数与超全局变量组合，标记为可疑\n");
            webshell = 1;  // 标记为可疑
            printf("DEBUG: 已设置 webshell = 1\n");
          }
        }
        
        // 改进：如果已经通过源代码模式匹配检测到webshell，即使跳过词法分析，也输出检测结果
        if (should_skip && webshell) {
          printf("\n========================================\n");
          printf("⚠️  警告: 检测到 WebShell!\n");
          printf("========================================\n");
          printf("文件: %s\n", ZSTR_VAL(filename));
          printf("检测方法: 源代码模式匹配（跳过词法分析以避免崩溃）\n");
          printf("原因: 文件包含可能导致词法分析器崩溃的复杂字符串，但通过源代码模式匹配检测到webshell特征\n");
          printf("========================================\n");
          zend_string_release(code);
          zend_string_release(filename);
          return 0;  // 返回0表示检测到webshell
        }
        
        if (should_skip) {
          // 不调用词法分析器，但如果没有检测到webshell，返回错误
          printf("\n========================================\n");
          printf("检测结果: 无法处理（词法分析器限制）\n");
          printf("========================================\n");
          printf("文件: %s\n", ZSTR_VAL(filename));
          printf("原因: 文件包含可能导致词法分析器崩溃的复杂字符串\n");
          printf("说明: 已进行源代码模式匹配检测，未发现明显的webshell特征\n");
          printf("建议: 使用其他检测工具或预处理文件后再检测\n");
          zend_string_release(code);
          zend_string_release(filename);
          return 1;
        }
        
        // 尝试进行词法分析
        printf("正在尝试词法分析（文件大小: %zu 字节，约 %zu 行）...\n", file_size, line_count_estimate);
        ast = zend_compile_string_to_ast(code, &ast_arena, filename);
        
        // 词法分析成功后，清除段错误处理中的文件信息
        g_file_size_on_segfault = 0;
        g_file_lines_on_segfault = 0;
        g_file_name_on_segfault = NULL;
        
        // 检查词法分析是否成功
        if (ast == NULL) {
            printf("\n错误: 词法分析失败，无法将PHP代码编译为AST\n");
            // 如果 AST 解析失败，但源代码中包含危险函数，仍然标记为可疑
            if (dangerous_count >= 2) {
              printf("警告: 虽然 AST 解析失败，但源代码中包含 %d 个危险函数/操作\n", dangerous_count);
              printf("检测结果: 可能是 WebShell（基于源代码模式匹配）\n");
              webshell = 1;  // 标记为可疑
            }
            printf("可能原因:\n");
            printf("  1. PHP代码存在语法错误\n");
            printf("  2. 文件过大或过于复杂，超出词法分析器处理能力\n");
            printf("  3. 文件包含特殊字符或编码问题\n");
            printf("  4. 文件开头不是PHP标签（如图片马：GIF89a等）\n");
            printf("文件信息: 大小 %zu 字节，约 %zu 行\n", file_size, line_count_estimate);
            
            // 如果通过源代码模式匹配检测到webshell，输出检测结果
            if (webshell) {
              printf("\n========================================\n");
              printf("⚠️  警告: 检测到 WebShell!\n");
              printf("========================================\n");
              printf("文件: %s\n", ZSTR_VAL(filename));
              printf("检测方法: 源代码模式匹配（词法分析失败）\n");
              if (is_image_webshell) {
                printf("原因: 检测到图片马特征（图片文件头后面跟着PHP webshell代码）\n");
              } else if (has_upload_webshell) {
                printf("原因: 检测到文件上传webshell特征（move_uploaded_file与超全局变量组合）\n");
              } else if (has_password_auth) {
                printf("原因: 检测到密码验证webshell特征（md5与超全局变量组合）\n");
              } else if (dangerous_count >= 2) {
                printf("原因: 源代码中包含 %d 个危险函数/操作\n", dangerous_count);
              } else {
                printf("原因: 通过源代码模式匹配检测到webshell特征\n");
              }
              printf("========================================\n");
              zend_string_release(code);
              zend_string_release(filename);
              if (current_filename) {
                  zend_string_release(current_filename);
              }
              return 0;  // 返回0表示检测到webshell
            }
            
            printf("\n========================================\n");
            printf("检测结果: 无法处理（词法分析失败）\n");
            printf("========================================\n");
            printf("文件: %s\n", ZSTR_VAL(filename));
            printf("原因: 词法分析器无法处理该文件\n");
            printf("说明: 已进行源代码模式匹配检测，未发现明显的webshell特征\n");
            printf("建议: 检查文件语法或使用其他检测工具\n");
            zend_string_release(code);
            zend_string_release(filename);
            if (current_filename) {
                zend_string_release(current_filename);
            }
            return 1;
        }

if (ast != NULL) {
    ast->father = NULL;
    g_root_ast = ast;
    
    // 检查 AST 节点数量（如果 AST 非常简单但文件很大，可能是非 PHP 文件）
    uint32_t ast_node_count = 0;
    if (ast && ast->kind == ZEND_AST_STMT_LIST) {
        zend_ast_list *stmt_list = zend_ast_get_list(ast);
        if (stmt_list) {
            ast_node_count = stmt_list->children;
        }
    }
    
    // 如果检测到 Perl 脚本或可疑脚本，且文件很大但 AST 节点很少，标记为可疑
    if (is_perl_script) {
        printf("警告: 检测到 Perl 脚本（shebang: #!/usr/bin/perl）\n");
    }
    if (is_suspicious_script && !is_perl_script) {
        printf("警告: 检测到文件包含多个可疑关键词（%d 个），可能是恶意脚本\n", keyword_count);
    }
    
    // 如果文件很大（>500字节）但 AST 节点很少（<=3），且包含可疑内容，可能是非 PHP 文件
    if (file_size > 500 && ast_node_count <= 3 && (is_perl_script || is_suspicious_script)) {
        printf("警告: 文件大小 %zu 字节，但 AST 节点数量很少（%u 个），可能是非 PHP 文件\n", 
               file_size, ast_node_count);
        printf("检测到可疑脚本文件（可能是 Perl、Python 或其他脚本语言）\n");
        printf("\n========================================\n");
        printf("检测结果: 检测到可疑脚本（非 PHP 文件）\n");
        printf("========================================\n");
        printf("文件: %s\n", ZSTR_VAL(filename));
        if (is_perl_script) {
            printf("原因: 文件是 Perl 脚本（包含 #!/usr/bin/perl shebang）\n");
        } else {
            printf("原因: 文件包含可疑关键词，且 AST 节点数量异常少\n");
        }
        printf("建议: 该文件不是 PHP 文件，但可能是恶意脚本，建议使用其他工具检测\n");
        webshell = 1;  // 标记为可疑
    }

    // 先初始化 father 指针等
    traverse_ast(g_root_ast);
    
    // 构建静态调用图
    printf("正在构建静态调用图...\n");
    build_static_call_graph(g_root_ast);
    
    dynamic_function_analysis(g_root_ast);

    // 初始化tainted_table并添加已知危险函数
    HashTable var_table;
    zend_hash_init(&var_table, 8, NULL, NULL, 0);

    // 处理AST：此时 father 已经正确，可以安全使用 current->father
    traverse_and_modify_ast(g_root_ast, &ast_arena, &var_table);
    printf("AST插桩完成，重新建立父子关系...\n");
    traverse_ast(g_root_ast);

    // 设置 current_filename 的位置
    if (current_filename) {
        zend_string_release(current_filename);
    }
    current_filename = zend_string_copy(filename);

    const char *skip_probe = getenv("YZ_SKIP_RUNTIME_PROBE");
    if (!skip_probe || strcmp(skip_probe, "1") != 0) {
        printf("执行带有防御逻辑的脚本以辅助动态确认...\n");
        export_and_run(g_root_ast ? g_root_ast : ast, argv[1]);
        
        // ★★ 新增：运行结束后，把 /tmp/yz_dyn_cg.jsonl 中的信息回填到调用图 / sink 表 ★★
        load_dynamic_edges_and_update_graph("/tmp/yz_dyn_cg.jsonl");
    } else {
        printf("检测到环境变量 YZ_SKIP_RUNTIME_PROBE=1，跳过运行时插桩执行。\n");
    }

    // 建议1：合并静态和动态调用图
    printf("正在合并静态和动态调用图...\n");
    merge_call_graphs();

    // 进行污点追踪和Webshell检测
    printf("正在进行污点分析...\n");
    taint_track(g_root_ast ? g_root_ast : ast);
    
    printf("正在进行Sink点分析...\n");
    sink_track(g_root_ast ? g_root_ast : ast, &sink_var_table, &sink_var_count);
    
    // 建议2：基于调用图的全局污点分析
    global_taint_analysis_with_cg();
    
    printf("正在进行Webshell检测...\n");
    // 添加调试信息：检查 AST 根节点
    if (g_root_ast) {
      printf("DEBUG: 使用 g_root_ast，kind=%d\n", g_root_ast->kind);
      if (g_root_ast->kind == ZEND_AST_STMT_LIST) {
        zend_ast_list *stmt_list = zend_ast_get_list(g_root_ast);
        printf("DEBUG: STMT_LIST 包含 %u 个语句\n", stmt_list->children);
        for (uint32_t i = 0; i < stmt_list->children && i < 10; i++) {
          if (stmt_list->child[i]) {
            printf("DEBUG: 语句 %u: kind=%d\n", i, stmt_list->child[i]->kind);
          }
        }
      }
    } else if (ast) {
      printf("DEBUG: 使用 ast，kind=%d\n", ast->kind);
      if (ast->kind == ZEND_AST_STMT_LIST) {
        zend_ast_list *stmt_list = zend_ast_get_list(ast);
        printf("DEBUG: STMT_LIST 包含 %u 个语句\n", stmt_list->children);
        for (uint32_t i = 0; i < stmt_list->children && i < 10; i++) {
          if (stmt_list->child[i]) {
            printf("DEBUG: 语句 %u: kind=%d\n", i, stmt_list->child[i]->kind);
          }
        }
      }
    } else {
      printf("DEBUG: 警告：AST 为空！\n");
    }
    webshell_check(g_root_ast ? g_root_ast : ast, 0);
    
    printf("----------------------------------------\n");
    
    /* TODO 2: 在检测结果里单独打印 suspect_site_table */
    printf("动态确认的危险调用点:\n");
    if (zend_hash_num_elements(&suspect_site_table) > 0) {
        zend_string *key;
        zval *val;
        ZEND_HASH_FOREACH_STR_KEY_VAL(&suspect_site_table, key, val) {
            if (key && val && Z_TYPE_P(val) == IS_STRING) {
                printf("  - %s: %s\n", ZSTR_VAL(key), Z_STRVAL_P(val));
            }
        } ZEND_HASH_FOREACH_END();
    } else {
        printf("  (无)\n");
    }
    printf("\n");
    
    /* 打印静态调用图边 */
    printf("静态调用图边:\n");
    if (zend_hash_num_elements(&call_graph_static) > 0) {
        zend_string *caller_key;
        zval *caller_val;
        ZEND_HASH_FOREACH_STR_KEY_VAL(&call_graph_static, caller_key, caller_val) {
            if (caller_key && caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
                HashTable *callee_set = (HashTable *)Z_PTR_P(caller_val);
                if (callee_set && zend_hash_num_elements(callee_set) > 0) {
                    zend_string *callee_key;
                    ZEND_HASH_FOREACH_STR_KEY(callee_set, callee_key) {
                        printf("  - %s -> %s (静态)\n", ZSTR_VAL(caller_key), ZSTR_VAL(callee_key));
                    } ZEND_HASH_FOREACH_END();
                }
            }
        } ZEND_HASH_FOREACH_END();
    } else {
        printf("  (无)\n");
    }
    printf("\n");
    
    /* 打印动态补充的调用图边 */
    printf("动态补充的调用图边:\n");
    if (zend_hash_num_elements(&call_graph_extra) > 0) {
        zend_string *caller_key;
        zval *caller_val;
        ZEND_HASH_FOREACH_STR_KEY_VAL(&call_graph_extra, caller_key, caller_val) {
            if (caller_key && caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
                HashTable *callee_set = (HashTable *)Z_PTR_P(caller_val);
                if (callee_set && zend_hash_num_elements(callee_set) > 0) {
                    zend_string *callee_key;
                    ZEND_HASH_FOREACH_STR_KEY(callee_set, callee_key) {
                        printf("  - %s -> %s (动态)\n", ZSTR_VAL(caller_key), ZSTR_VAL(callee_key));
                    } ZEND_HASH_FOREACH_END();
                }
            }
        } ZEND_HASH_FOREACH_END();
    } else {
        printf("  (无)\n");
    }
    printf("\n");
    
    /* 建议4：在最终webshell结论里，显式考虑 call_graph_extra / suspect_site_table */
    int dynamic_path_found = 0;
    /* 检查动态调用图中是否存在从入口到危险函数的路径 */
    if (zend_hash_num_elements(&call_graph_extra) > 0) {
        zend_string *caller_key;
        zval *caller_val;
        ZEND_HASH_FOREACH_STR_KEY_VAL(&call_graph_extra, caller_key, caller_val) {
            if (caller_key && caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
                HashTable *callee_set = (HashTable *)Z_PTR_P(caller_val);
                if (callee_set) {
                    zend_string *callee_key;
                    ZEND_HASH_FOREACH_STR_KEY(callee_set, callee_key) {
                        if (callee_key && is_known_sink_function(callee_key)) {
                            const char *caller_name = ZSTR_VAL(caller_key);
                            /* 检查是否是入口函数（__main__）或已知的调用者 */
                            if (strcmp(caller_name, "__main__") == 0) {
                                dynamic_path_found = 1;
                                printf("动态确认路径: %s -> %s (通过动态执行补充)\n", 
                                       caller_name, ZSTR_VAL(callee_key));
                            }
                        }
                    } ZEND_HASH_FOREACH_END();
                }
            }
        } ZEND_HASH_FOREACH_END();
    }
    
    /* 建议4：动态断言命中则强制标记为 Webshell */
    if (dynamic_webshell_hit > 0) {
        printf("\n========================================\n");
        printf("动态检测：命中断言 %d 次，判定为 WebShell\n", dynamic_webshell_hit);
        printf("========================================\n");
        webshell = 1;
    }
    
    /* 检查 suspect_site_table 中是否有 ASSERT_FAIL/EVAL/SINK_HIT */
    int suspect_count = 0;
    if (zend_hash_num_elements(&suspect_site_table) > 0) {
        zend_string *key;
        zval *val;
        ZEND_HASH_FOREACH_STR_KEY_VAL(&suspect_site_table, key, val) {
            if (key && val && Z_TYPE_P(val) == IS_STRING) {
                const char *reason = Z_STRVAL_P(val);
                if (strstr(reason, "ASSERT_FAIL") || strstr(reason, "EVAL") || strstr(reason, "SINK_HIT")) {
                    suspect_count++;
                }
            }
        } ZEND_HASH_FOREACH_END();
    }
    
    if (suspect_count > 0 && dynamic_webshell_hit == 0) {
        printf("\n动态检测：发现 %d 处可疑调用点，标记为高危可疑\n", suspect_count);
        /* 可以根据需要决定是否也标记为webshell */
    }
    
    printf("检测结果:\n");
    // 最终检查：如果源代码模式匹配检测到了危险函数组合，确保 webshell 被设置
    // 注意：code 变量可能已经释放，需要重新读取文件或使用之前保存的值
    // 为了安全起见，我们在这里再次检查（如果 code 仍然有效）
    printf("DEBUG: webshell=%d, dynamic_path_found=%d, global_dynamic_path_detected=%d, dynamic_webshell_hit=%d, suspect_site_table_size=%u\n",
           webshell, dynamic_path_found, global_dynamic_path_detected, dynamic_webshell_hit, 
           zend_hash_num_elements(&suspect_site_table));
    if (webshell || dynamic_path_found || global_dynamic_path_detected || 
        dynamic_webshell_hit > 0 || zend_hash_num_elements(&suspect_site_table) > 0) {
        printf("⚠️  警告: 检测到 WebShell!\n");
        printf("该文件包含危险的代码模式，可能被用于恶意目的。\n");
        if (dynamic_webshell_hit > 0) {
            printf("动态断言拦截到 %d 次可疑调用，直接判定为恶意。\n", dynamic_webshell_hit);
        }
        if (dynamic_path_found) {
            printf("通过动态执行补充调用图，发现从入口到危险函数的调用路径（变量函数形式），因此将该样本判定为 Webshell。\n");
        }
        if (global_dynamic_path_detected) {
            printf("通过调用图路径搜索，发现从入口到危险函数的调用路径。\n");
        }
        if (zend_hash_num_elements(&suspect_site_table) > 0) {
            printf("动态确认了 %u 处危险调用点（eval等）。\n",
                   zend_hash_num_elements(&suspect_site_table));
        }
    } else {
        printf("✓ 未检测到 WebShell\n");
        printf("该文件看起来是正常的PHP代码。\n");
    }
    printf("========================================\n");
 
 //
 
 
    // 清理
    zend_hash_destroy(&var_table);
    // source 已经在前面 free 过了，这里不需要再次 free
    // free(source);  // 删除：避免 double free
    zend_string_release(filename);
    zend_string_release(code);
    
    // 清理哈希表
    zend_hash_destroy(&tainted_table);
    zend_hash_destroy(&local_tainted_table);
    zend_hash_destroy(&var_source_table);
    zend_hash_destroy(&func_source_table);
    zend_hash_destroy(&sink_table);
    zend_hash_destroy(&sink_var_table);
    zend_hash_destroy(&var_value_table);
    zend_hash_destroy(&sink_func_table);
    zend_hash_destroy(&local_sink_table);
    zend_hash_destroy(&webshell_table);
    //suspect_site_table 清理
    zend_hash_destroy(&suspect_site_table);
    //call_graph_extra 清理（需要先清理内部的 HashTable）
    zend_string *caller_key;
    zval *caller_val;
    ZEND_HASH_FOREACH_STR_KEY_VAL(&call_graph_extra, caller_key, caller_val) {
        if (caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
            HashTable *callee_set = (HashTable *)Z_PTR_P(caller_val);
            if (callee_set) {
                zend_hash_destroy(callee_set);
                efree(callee_set);
            }
        }
    } ZEND_HASH_FOREACH_END();
    zend_hash_destroy(&call_graph_extra);
    //call_graph_static 清理（需要先清理内部的 HashTable）
    ZEND_HASH_FOREACH_STR_KEY_VAL(&call_graph_static, caller_key, caller_val) {
        if (caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
            HashTable *callee_set = (HashTable *)Z_PTR_P(caller_val);
            if (callee_set) {
                zend_hash_destroy(callee_set);
                efree(callee_set);
            }
        }
    } ZEND_HASH_FOREACH_END();
    zend_hash_destroy(&call_graph_static);
    //merged_call_graph 清理（需要先清理内部的 HashTable）
    ZEND_HASH_FOREACH_STR_KEY_VAL(&merged_call_graph, caller_key, caller_val) {
        if (caller_val && Z_TYPE_P(caller_val) == IS_PTR) {
            HashTable *callee_set = (HashTable *)Z_PTR_P(caller_val);
            if (callee_set) {
                zend_hash_destroy(callee_set);
                efree(callee_set);
            }
        }
    } ZEND_HASH_FOREACH_END();
    zend_hash_destroy(&merged_call_graph);
} else {
    printf("----------------------------------------\n");
    printf("错误: PHP代码存在语法错误，无法进行分析\n");
    printf("========================================\n");
    return 1;
}

  // 返回适当的退出码：0表示正常，1表示检测到Webshell或错误
  return webshell ? 1 : 0;
}

