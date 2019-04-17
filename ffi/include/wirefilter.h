#ifndef _WIREFILTER_H_
#define _WIREFILTER_H_

#include <stdlib.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct wirefilter_scheme wirefilter_scheme_t;
typedef struct wirefilter_execution_context wirefilter_execution_context_t;
typedef struct wirefilter_filter_ast wirefilter_filter_ast_t;
typedef struct wirefilter_filter wirefilter_filter_t;

typedef struct {
    const char *data;
    size_t length;
} wirefilter_rust_allocated_str_t;

typedef struct {
    const char *data;
    size_t length;
} wirefilter_static_rust_allocated_str_t;

typedef struct {
    const char *data;
    size_t length;
} wirefilter_externally_allocated_str_t;

typedef struct {
    const unsigned char *data;
    size_t length;
} wirefilter_externally_allocated_byte_arr_t;

typedef union {
    uint8_t success;
    struct {
        uint8_t _res1;
        wirefilter_rust_allocated_str_t msg;
    } err;
    struct {
        uint8_t _res2;
        wirefilter_filter_ast_t *ast;
    } ok;
} wirefilter_parsing_result_t;

typedef enum {
    WIREFILTER_TYPE_IP,
    WIREFILTER_TYPE_BYTES,
    WIREFILTER_TYPE_INT,
    WIREFILTER_TYPE_BOOL,
} wirefilter_type_t;

wirefilter_scheme_t *wirefilter_create_scheme();
void wirefilter_free_scheme(wirefilter_scheme_t *scheme);

void wirefilter_add_type_field_to_scheme(
    wirefilter_scheme_t *scheme,
    wirefilter_externally_allocated_str_t name,
    wirefilter_type_t type
);

wirefilter_parsing_result_t wirefilter_parse_filter(
    const wirefilter_scheme_t *scheme,
    wirefilter_externally_allocated_str_t input
);

void wirefilter_free_parsing_result(wirefilter_parsing_result_t result);

wirefilter_filter_t *wirefilter_compile_filter(wirefilter_filter_ast_t *ast);
void wirefilter_free_compiled_filter(wirefilter_filter_t *filter);

wirefilter_execution_context_t *wirefilter_create_execution_context(
    const wirefilter_scheme_t *scheme
);
void wirefilter_free_execution_context(
    wirefilter_execution_context_t *exec_ctx
);

void wirefilter_add_int_value_to_execution_context(
    wirefilter_execution_context_t *exec_ctx,
    wirefilter_externally_allocated_str_t name,
    int32_t value
);

void wirefilter_add_bytes_value_to_execution_context(
    wirefilter_execution_context_t *exec_ctx,
    wirefilter_externally_allocated_str_t name,
    wirefilter_externally_allocated_byte_arr_t value
);

void wirefilter_add_ipv6_value_to_execution_context(
    wirefilter_execution_context_t *exec_ctx,
    wirefilter_externally_allocated_str_t name,
    uint8_t value[16]
);

void wirefilter_add_ipv4_value_to_execution_context(
    wirefilter_execution_context_t *exec_ctx,
    wirefilter_externally_allocated_str_t name,
    uint8_t value[4]
);

void wirefilter_add_bool_value_to_execution_context(
    wirefilter_execution_context_t *exec_ctx,
    wirefilter_externally_allocated_str_t name,
    bool value
);

bool wirefilter_match(
    const wirefilter_filter_t *filter,
    const wirefilter_execution_context_t *exec_ctx
);

bool wirefilter_filter_uses(
    const wirefilter_filter_ast_t *ast,
    wirefilter_externally_allocated_str_t field_name
);

uint64_t wirefilter_get_filter_hash(const wirefilter_filter_ast_t *ast);

wirefilter_rust_allocated_str_t wirefilter_serialize_filter_to_json(
    const wirefilter_filter_ast_t *ast
);

void wirefilter_free_string(wirefilter_rust_allocated_str_t str);

wirefilter_static_rust_allocated_str_t wirefilter_get_version();

#ifdef __cplusplus
}
#endif

#endif // _WIREFILTER_H_
