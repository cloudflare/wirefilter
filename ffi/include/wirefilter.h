#ifndef _WIREFILTER_H_
#define _WIREFILTER_H_

/* Generated with cbindgen:0.27.0 */

/* Warning, this file is autogenerated by cbindgen. Don't modify this manually. */

#include <stdarg.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

enum wirefilter_primitive_type
#ifdef __cplusplus
  : uint8_t
#endif // __cplusplus
 {
  WIREFILTER_PRIMITIVE_TYPE_IP = 1,
  WIREFILTER_PRIMITIVE_TYPE_BYTES = 2,
  WIREFILTER_PRIMITIVE_TYPE_INT = 3,
  WIREFILTER_PRIMITIVE_TYPE_BOOL = 4,
};
#ifndef __cplusplus
typedef uint8_t wirefilter_primitive_type;
#endif // __cplusplus

/**
 * Represents the status of an operation.
 */
enum wirefilter_status {
  /**
   * Operation succeeded.
   */
  WIREFILTER_STATUS_SUCCESS = 0,
  /**
   * Operation encountered an error.
   *
   * Use [`wirefilter_get_last_error`] to retrieve the error message.
   */
  WIREFILTER_STATUS_ERROR,
  /**
   * Operation has triggered a panic.
   *
   * Use [`wirefilter_get_last_error`] to retrieve the panic information.
   */
  WIREFILTER_STATUS_PANIC,
};

struct wirefilter_array;

struct wirefilter_execution_context;

struct wirefilter_filter;

struct wirefilter_filter_ast;

struct wirefilter_map;

struct wirefilter_scheme;

struct wirefilter_scheme_builder;

struct wirefilter_type {
  uint32_t layers;
  uint8_t len;
  uint8_t primitive;
};

struct wirefilter_rust_allocated_str {
  char *ptr;
  size_t len;
};

struct wirefilter_parsing_result {
  enum wirefilter_status status;
  struct wirefilter_filter_ast *ast;
};

struct wirefilter_hashing_result {
  enum wirefilter_status status;
  uint64_t hash;
};

struct wirefilter_serializing_result {
  enum wirefilter_status status;
  struct wirefilter_rust_allocated_str json;
};

struct wirefilter_compiling_result {
  enum wirefilter_status status;
  struct wirefilter_filter *filter;
};

struct wirefilter_matching_result {
  enum wirefilter_status status;
  bool matched;
};

struct wirefilter_using_result {
  enum wirefilter_status status;
  bool used;
};

struct wirefilter_static_rust_allocated_str {
  const char *ptr;
  size_t len;
};

#ifdef __cplusplus
extern "C" {
#endif // __cplusplus

/**
 * Returns a pointer to the last error string if there was one or NULL.
 */
const char *wirefilter_get_last_error(void);

/**
 * Clears the last error string if there was one.
 *
 * Further calls to `wirefilter_get_last_error` will return NULL,
 * until another error is written to it.
 */
void wirefilter_clear_last_error(void);

struct wirefilter_scheme_builder *wirefilter_create_scheme_builder(void);

void wirefilter_free_scheme_builder(struct wirefilter_scheme_builder *scheme);

struct wirefilter_type wirefilter_create_primitive_type(wirefilter_primitive_type ty);

struct wirefilter_type wirefilter_create_map_type(struct wirefilter_type ty);

struct wirefilter_type wirefilter_create_array_type(struct wirefilter_type ty);

bool wirefilter_add_type_field_to_scheme(struct wirefilter_scheme_builder *builder,
                                         const char *name_ptr,
                                         size_t name_len,
                                         struct wirefilter_type ty);

bool wirefilter_add_always_list_to_scheme(struct wirefilter_scheme_builder *builder,
                                          struct wirefilter_type ty);

bool wirefilter_add_never_list_to_scheme(struct wirefilter_scheme_builder *builder,
                                         struct wirefilter_type ty);

struct wirefilter_scheme *wirefilter_build_scheme(struct wirefilter_scheme_builder *builder);

void wirefilter_free_scheme(struct wirefilter_scheme *scheme);

void wirefilter_free_string(struct wirefilter_rust_allocated_str s);

struct wirefilter_parsing_result wirefilter_parse_filter(const struct wirefilter_scheme *scheme,
                                                         const char *input_ptr,
                                                         size_t input_len);

void wirefilter_free_parsed_filter(struct wirefilter_filter_ast *ast);

struct wirefilter_hashing_result wirefilter_get_filter_hash(const struct wirefilter_filter_ast *filter_ast);

struct wirefilter_serializing_result wirefilter_serialize_filter_to_json(const struct wirefilter_filter_ast *filter_ast);

struct wirefilter_serializing_result wirefilter_serialize_scheme_to_json(const struct wirefilter_scheme *scheme);

struct wirefilter_serializing_result wirefilter_serialize_type_to_json(struct wirefilter_type ty);

struct wirefilter_execution_context *wirefilter_create_execution_context(const struct wirefilter_scheme *scheme);

struct wirefilter_serializing_result wirefilter_serialize_execution_context_to_json(struct wirefilter_execution_context *exec_context);

bool wirefilter_deserialize_json_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                      const uint8_t *json_ptr,
                                                      size_t json_len);

void wirefilter_free_execution_context(struct wirefilter_execution_context *exec_context);

bool wirefilter_add_int_value_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                   const char *name_ptr,
                                                   size_t name_len,
                                                   int64_t value);

bool wirefilter_add_bytes_value_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                     const char *name_ptr,
                                                     size_t name_len,
                                                     const uint8_t *value_ptr,
                                                     size_t value_len);

bool wirefilter_add_ipv6_value_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                    const char *name_ptr,
                                                    size_t name_len,
                                                    const uint8_t (*value)[16]);

bool wirefilter_add_ipv4_value_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                    const char *name_ptr,
                                                    size_t name_len,
                                                    const uint8_t (*value)[4]);

bool wirefilter_add_bool_value_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                    const char *name_ptr,
                                                    size_t name_len,
                                                    bool value);

bool wirefilter_add_map_value_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                   const char *name_ptr,
                                                   size_t name_len,
                                                   struct wirefilter_map *value);

bool wirefilter_add_array_value_to_execution_context(struct wirefilter_execution_context *exec_context,
                                                     const char *name_ptr,
                                                     size_t name_len,
                                                     struct wirefilter_array *value);

struct wirefilter_map *wirefilter_create_map(struct wirefilter_type ty);

bool wirefilter_add_int_value_to_map(struct wirefilter_map *map,
                                     const uint8_t *name_ptr,
                                     size_t name_len,
                                     int64_t value);

bool wirefilter_add_bytes_value_to_map(struct wirefilter_map *map,
                                       const uint8_t *name_ptr,
                                       size_t name_len,
                                       const uint8_t *value_ptr,
                                       size_t value_len);

bool wirefilter_add_ipv6_value_to_map(struct wirefilter_map *map,
                                      const uint8_t *name_ptr,
                                      size_t name_len,
                                      const uint8_t (*value)[16]);

bool wirefilter_add_ipv4_value_to_map(struct wirefilter_map *map,
                                      const uint8_t *name_ptr,
                                      size_t name_len,
                                      const uint8_t (*value)[4]);

bool wirefilter_add_bool_value_to_map(struct wirefilter_map *map,
                                      const uint8_t *name_ptr,
                                      size_t name_len,
                                      bool value);

bool wirefilter_add_map_value_to_map(struct wirefilter_map *map,
                                     const uint8_t *name_ptr,
                                     size_t name_len,
                                     struct wirefilter_map *value);

bool wirefilter_add_array_value_to_map(struct wirefilter_map *map,
                                       const uint8_t *name_ptr,
                                       size_t name_len,
                                       struct wirefilter_array *value);

void wirefilter_free_map(struct wirefilter_map *map);

struct wirefilter_array *wirefilter_create_array(struct wirefilter_type ty);

bool wirefilter_add_int_value_to_array(struct wirefilter_array *array,
                                       uint32_t index,
                                       int64_t value);

bool wirefilter_add_bytes_value_to_array(struct wirefilter_array *array,
                                         uint32_t index,
                                         const uint8_t *value_ptr,
                                         size_t value_len);

bool wirefilter_add_ipv6_value_to_array(struct wirefilter_array *array,
                                        uint32_t index,
                                        const uint8_t (*value)[16]);

bool wirefilter_add_ipv4_value_to_array(struct wirefilter_array *array,
                                        uint32_t index,
                                        const uint8_t (*value)[4]);

bool wirefilter_add_bool_value_to_array(struct wirefilter_array *array, uint32_t index, bool value);

bool wirefilter_add_map_value_to_array(struct wirefilter_array *array,
                                       uint32_t index,
                                       struct wirefilter_map *value);

bool wirefilter_add_array_value_to_array(struct wirefilter_array *array,
                                         uint32_t index,
                                         struct wirefilter_array *value);

void wirefilter_free_array(struct wirefilter_array *array);

struct wirefilter_compiling_result wirefilter_compile_filter(struct wirefilter_filter_ast *filter_ast);

struct wirefilter_matching_result wirefilter_match(const struct wirefilter_filter *filter,
                                                   const struct wirefilter_execution_context *exec_context);

void wirefilter_free_compiled_filter(struct wirefilter_filter *filter);

struct wirefilter_using_result wirefilter_filter_uses(const struct wirefilter_filter_ast *filter_ast,
                                                      const char *field_name_ptr,
                                                      size_t field_name_len);

struct wirefilter_using_result wirefilter_filter_uses_list(const struct wirefilter_filter_ast *filter_ast,
                                                           const char *field_name_ptr,
                                                           size_t field_name_len);

struct wirefilter_static_rust_allocated_str wirefilter_get_version(void);

void wirefilter_set_panic_catcher_hook(void);

bool wirefilter_set_panic_catcher_fallback_mode(uint8_t fallback_mode);

void wirefilter_enable_panic_catcher(void);

void wirefilter_disable_panic_catcher(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  /* _WIREFILTER_H_ */
