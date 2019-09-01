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
typedef struct wirefilter_map wirefilter_map_t;
typedef struct wirefilter_array wirefilter_array_t;

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
    WIREFILTER_TYPE_TAG_IP,
    WIREFILTER_TYPE_TAG_BYTES,
    WIREFILTER_TYPE_TAG_INT,
    WIREFILTER_TYPE_TAG_BOOL,
    WIREFILTER_TYPE_TAG_ARRAY,
    WIREFILTER_TYPE_TAG_MAP,
} wirefilter_type_tag_t;

typedef struct {
    uint8_t tag;
    void *data;
} wirefilter_type_t;

static const wirefilter_type_t WIREFILTER_TYPE_IP = {.tag = WIREFILTER_TYPE_TAG_IP, .data = NULL};
static const wirefilter_type_t WIREFILTER_TYPE_BYTES = {.tag = WIREFILTER_TYPE_TAG_BYTES, .data = NULL};
static const wirefilter_type_t WIREFILTER_TYPE_INT = {.tag = WIREFILTER_TYPE_TAG_INT, .data = NULL};
static const wirefilter_type_t WIREFILTER_TYPE_BOOL = {.tag = WIREFILTER_TYPE_TAG_BOOL, .data = NULL};

wirefilter_scheme_t *wirefilter_create_scheme();
void wirefilter_free_scheme(wirefilter_scheme_t *scheme);

wirefilter_type_t wirefilter_create_map_type(wirefilter_type_t type);

wirefilter_type_t wirefilter_create_array_type(wirefilter_type_t type);

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

void wirefilter_add_map_value_to_execution_context(
    wirefilter_execution_context_t *exec_ctx,
    wirefilter_externally_allocated_str_t name,
    wirefilter_map_t *map
);

void wirefilter_add_array_value_to_execution_context(
    wirefilter_execution_context_t *exec_ctx,
    wirefilter_externally_allocated_str_t name,
    wirefilter_array_t *array
);

wirefilter_map_t *wirefilter_create_map(wirefilter_type_t type);

void wirefilter_add_int_value_to_map(
    wirefilter_map_t *map,
    wirefilter_externally_allocated_str_t name,
    int32_t value
);

void wirefilter_add_bytes_value_to_map(
    wirefilter_map_t *map,
    wirefilter_externally_allocated_str_t name,
    wirefilter_externally_allocated_byte_arr_t value
);

void wirefilter_add_ipv6_value_to_map(
    wirefilter_map_t *map,
    wirefilter_externally_allocated_str_t name,
    uint8_t value[16]
);

void wirefilter_add_ipv4_value_to_map(
    wirefilter_map_t *map,
    wirefilter_externally_allocated_str_t name,
    uint8_t value[4]
);

void wirefilter_add_bool_value_to_map(
    wirefilter_map_t *map,
    wirefilter_externally_allocated_str_t name,
    bool value
);

void wirefilter_add_map_value_to_map(
    wirefilter_map_t *map,
    wirefilter_externally_allocated_str_t name,
    wirefilter_map_t *value
);

void wirefilter_add_array_value_to_map(
    wirefilter_map_t *map,
    wirefilter_externally_allocated_str_t name,
    wirefilter_array_t *value
);

void wirefilter_free_map(wirefilter_map_t *map);

wirefilter_array_t *wirefilter_create_array(wirefilter_type_t type);

void wirefilter_add_int_value_to_array(
    wirefilter_array_t *array,
    uint32_t index,
    int32_t value
);

void wirefilter_add_bytes_value_to_array(
    wirefilter_array_t *array,
    uint32_t index,
    wirefilter_externally_allocated_byte_arr_t value
);

void wirefilter_add_ipv6_value_to_array(
    wirefilter_array_t *array,
    uint32_t index,
    uint8_t value[16]
);

void wirefilter_add_ipv4_value_to_array(
    wirefilter_array_t *array,
    uint32_t index,
    uint8_t value[4]
);

void wirefilter_add_bool_value_to_array(
    wirefilter_array_t *array,
    uint32_t index,
    bool value
);

void wirefilter_add_map_value_to_array(
    wirefilter_array_t *array,
    uint32_t index,
    wirefilter_map_t *value
);

void wirefilter_add_array_value_to_array(
    wirefilter_array_t *array,
    uint32_t index,
    wirefilter_array_t *value
);

void wirefilter_free_array(wirefilter_array_t *array);

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
