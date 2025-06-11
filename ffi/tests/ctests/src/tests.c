#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stdio.h>

#include <wirefilter.h>

extern void rust_assert(bool check, const char *msg);

#define STRING(s) s, strlen(s)
#define BYTES(s) (unsigned char *)s, strlen(s)

#define WIREFILTER_TYPE_BYTES (wirefilter_create_primitive_type(WIREFILTER_PRIMITIVE_TYPE_BYTES))
#define WIREFILTER_TYPE_IP (wirefilter_create_primitive_type(WIREFILTER_PRIMITIVE_TYPE_IP))
#define WIREFILTER_TYPE_BOOL (wirefilter_create_primitive_type(WIREFILTER_PRIMITIVE_TYPE_BOOL))
#define WIREFILTER_TYPE_INT (wirefilter_create_primitive_type(WIREFILTER_PRIMITIVE_TYPE_INT))

void initialize_scheme(struct wirefilter_scheme_builder *builder) {
    rust_assert(wirefilter_add_type_field_to_scheme(
        builder,
        STRING("http.host"),
        WIREFILTER_TYPE_BYTES
    ), "could not add field http.host of type \"Bytes\" to scheme");
    rust_assert(wirefilter_add_type_field_to_scheme(
        builder,
        STRING("ip.src"),
        WIREFILTER_TYPE_IP
    ), "could not add field ip.src of type \"Ip\" to scheme");
    rust_assert(wirefilter_add_type_field_to_scheme(
        builder,
        STRING("ip.dst"),
        WIREFILTER_TYPE_IP
    ), "could not add field ip.dst of type \"Ip\" to scheme");
    rust_assert(wirefilter_add_type_field_to_scheme(
        builder,
        STRING("ssl"),
        WIREFILTER_TYPE_BOOL
    ), "could not add field ssl of type \"Bool\" to scheme");
    rust_assert(wirefilter_add_type_field_to_scheme(
        builder,
        STRING("tcp.port"),
        WIREFILTER_TYPE_INT
    ), "could not add field tcp.port of type \"Int\" to scheme");
    wirefilter_add_type_field_to_scheme(
        builder,
        STRING("http.headers"),
        wirefilter_create_map_type(WIREFILTER_TYPE_BYTES)
    );
    rust_assert(wirefilter_add_type_field_to_scheme(
        builder,
        STRING("http.cookies"),
        wirefilter_create_array_type(WIREFILTER_TYPE_BYTES)
    ), "could not add field http.cookies of type \"Array<Bytes>\" to scheme");
    rust_assert(wirefilter_add_always_list_to_scheme(
        builder,
        WIREFILTER_TYPE_IP
    ), "could not add list for type \"Ip\" to scheme");
}

struct wirefilter_scheme *build_scheme() {
    struct wirefilter_scheme_builder *builder = wirefilter_create_scheme_builder();
    rust_assert(builder != NULL, "could not create scheme builder");

    initialize_scheme(builder);

    return wirefilter_build_scheme(builder);
}

void wirefilter_ffi_ctest_create_array_type() {
    struct wirefilter_type array_type = wirefilter_create_array_type(WIREFILTER_TYPE_BYTES);
    rust_assert(array_type.layers == 0, "could not create valid array type");
    rust_assert(array_type.len == 1, "could not create valid array type");
    rust_assert(array_type.primitive == WIREFILTER_PRIMITIVE_TYPE_BYTES, "could not create valid array type");
}

void wirefilter_ffi_ctest_create_map_type() {
    struct wirefilter_type map_type = wirefilter_create_map_type(WIREFILTER_TYPE_BYTES);
    rust_assert(map_type.layers == 1, "could not create valid map type");
    rust_assert(map_type.len == 1, "could not create valid map type");
    rust_assert(map_type.primitive == WIREFILTER_PRIMITIVE_TYPE_BYTES, "could not create valid map type");
}

void wirefilter_ffi_ctest_create_complex_type() {
    struct wirefilter_type type = WIREFILTER_TYPE_BYTES;
    type = wirefilter_create_map_type(type);
    type = wirefilter_create_array_type(type);
    rust_assert(type.layers == 2, "could not create valid type");
    rust_assert(type.len == 2, "could not create valid type");
    rust_assert(type.primitive == WIREFILTER_PRIMITIVE_TYPE_BYTES, "could not create valid type");

    type = WIREFILTER_TYPE_BYTES;
    type = wirefilter_create_array_type(type);
    type = wirefilter_create_map_type(type);
    rust_assert(type.layers == 1, "could not create valid type");
    rust_assert(type.len == 2, "could not create valid type");
    rust_assert(type.primitive == WIREFILTER_PRIMITIVE_TYPE_BYTES, "could not create valid type");
}

void wirefilter_ffi_ctest_create_scheme_builder() {
    struct wirefilter_scheme_builder *builder = wirefilter_create_scheme_builder();
    rust_assert(builder != NULL, "could not create scheme builder");
    wirefilter_free_scheme_builder(builder);
}

void wirefilter_ffi_ctest_add_fields_to_scheme() {
    struct wirefilter_scheme_builder *builder = wirefilter_create_scheme_builder();
    rust_assert(builder != NULL, "could not create scheme builder");

    initialize_scheme(builder);

    wirefilter_free_scheme_builder(builder);
}

void wirefilter_ffi_ctest_add_malloced_type_field_to_scheme() {
    struct wirefilter_scheme_builder *builder = wirefilter_create_scheme_builder();
    rust_assert(builder != NULL, "could not create scheme builder");

    struct wirefilter_type *byte_type = (struct wirefilter_type *)malloc(sizeof(struct wirefilter_type));
    rust_assert(byte_type != NULL, "could not allocate type");
    *byte_type = WIREFILTER_TYPE_BYTES;

    rust_assert(wirefilter_add_type_field_to_scheme(
        builder,
        STRING("http.host"),
        *byte_type
    ), "could not add field http.host of type \"Bytes\" to scheme");

    free(byte_type);

    wirefilter_free_scheme_builder(builder);
}

void wirefilter_ffi_ctest_parse_good_filter() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port == 80")
    );
    rust_assert(result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result.ast != NULL, "could not parse good filter");

    wirefilter_free_parsed_filter(result.ast);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_parse_bad_filter() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port == \"wirefilter\"")
    );
    rust_assert(result.status != WIREFILTER_STATUS_SUCCESS, "should not parse bad filter");
    rust_assert(wirefilter_get_last_error() != NULL, "missing error message");

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_filter_uses_field() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result parsing_result = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port == 80")
    );
    rust_assert(parsing_result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(parsing_result.ast != NULL, "could not parse good filter");

    struct wirefilter_using_result using_result;

    using_result = wirefilter_filter_uses(
        parsing_result.ast,
        STRING("tcp.port")
    );

    rust_assert(using_result.status == WIREFILTER_STATUS_SUCCESS, "could not check if filter uses tcp.port field");
    rust_assert(using_result.used == true, "filter should be using field tcp.port");

    using_result = wirefilter_filter_uses(
        parsing_result.ast,
        STRING("ip.src")
    );

    rust_assert(using_result.status == WIREFILTER_STATUS_SUCCESS, "could not check if filter uses ip.src field");
    rust_assert(using_result.used == false, "filter should not be using field ip.src");

   wirefilter_free_parsed_filter(parsing_result.ast);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_filter_uses_list_field() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result parsing_result = wirefilter_parse_filter(
        scheme,
        STRING("ip.src in $bad")
    );
    rust_assert(parsing_result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(parsing_result.ast != NULL, "could not parse good filter");

    struct wirefilter_using_result using_result;

    using_result = wirefilter_filter_uses_list(
        parsing_result.ast,
        STRING("ip.src")
    );

    rust_assert(using_result.status == WIREFILTER_STATUS_SUCCESS, "could not check if filter uses tcp.port field");
    rust_assert(using_result.used == true, "filter should be using field ip.src");

    using_result = wirefilter_filter_uses_list(
        parsing_result.ast,
        STRING("tcp.port")
    );

    rust_assert(using_result.status == WIREFILTER_STATUS_SUCCESS, "could not check if filter uses tcp.port field");
    rust_assert(using_result.used == false, "filter should not be using field tcp.port");

    wirefilter_free_parsed_filter(parsing_result.ast);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_filter_hash() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result1 = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port == 80")
    );
    rust_assert(result1.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result1.ast != NULL, "could not parse good filter");

    struct wirefilter_parsing_result result2 = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port              ==80")
    );
    rust_assert(result2.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result2.ast != NULL, "could not parse good filter");

    struct wirefilter_hashing_result hashing_result;

    hashing_result = wirefilter_get_filter_hash(result1.ast);
    rust_assert(hashing_result.status == WIREFILTER_STATUS_SUCCESS, "could not compute hash");
    uint64_t hash1 = hashing_result.hash;

    hashing_result = wirefilter_get_filter_hash(result2.ast);
    rust_assert(hashing_result.status == WIREFILTER_STATUS_SUCCESS, "could not compute hash");
    uint64_t hash2 = hashing_result.hash;

    rust_assert(hash1 == hash2, "both filters should have the same hash");

    wirefilter_free_parsed_filter(result1.ast);

    wirefilter_free_parsed_filter(result2.ast);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_filter_serialize() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port == 80")
    );
    rust_assert(result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result.ast != NULL, "could not parse good filter");

    struct wirefilter_serializing_result serializing_result = wirefilter_serialize_filter_to_json(result.ast);
    rust_assert(serializing_result.status == WIREFILTER_STATUS_SUCCESS, "could not serialize filter to JSON");

    struct wirefilter_rust_allocated_str json = serializing_result.json;
    rust_assert(json.ptr != NULL && json.len > 0, "could not serialize filter to JSON");

    rust_assert(
        strncmp(json.ptr, "{\"lhs\":\"tcp.port\",\"op\":\"Equal\",\"rhs\":80}", json.len) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_free_parsed_filter(result.ast);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_scheme_serialize() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_serializing_result serializing_result = wirefilter_serialize_scheme_to_json(scheme);
    rust_assert(serializing_result.status == WIREFILTER_STATUS_SUCCESS, "could not serialize scheme to JSON");

    struct wirefilter_rust_allocated_str json = serializing_result.json;
    rust_assert(json.ptr != NULL && json.len > 0, "could not serialize scheme to JSON");

    rust_assert(
        strncmp(json.ptr, "{\"http.host\":\"Bytes\",\"ip.src\":\"Ip\",\"ip.dst\":\"Ip\",\"ssl\":\"Bool\",\"tcp.port\":\"Int\",\"http.headers\":{\"Map\":\"Bytes\"},\"http.cookies\":{\"Array\":\"Bytes\"}}", json.len) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_type_serialize() {
    struct wirefilter_serializing_result serializing_result = wirefilter_serialize_type_to_json(WIREFILTER_TYPE_BYTES);
    rust_assert(serializing_result.status == WIREFILTER_STATUS_SUCCESS, "could not serialize type to JSON");

    struct wirefilter_rust_allocated_str json = serializing_result.json;
    rust_assert(json.ptr != NULL && json.len > 0, "could not serialize type to JSON");

    rust_assert(
        strncmp(json.ptr, "\"Bytes\"", json.len) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    struct wirefilter_type type = wirefilter_create_map_type(
        wirefilter_create_array_type(WIREFILTER_TYPE_BYTES)
    );

    serializing_result = wirefilter_serialize_type_to_json(type);
    rust_assert(serializing_result.status == WIREFILTER_STATUS_SUCCESS, "could not serialize type to JSON");

    json = serializing_result.json;
    rust_assert(json.ptr != NULL && json.len > 0, "could not serialize type to JSON");

    rust_assert(
        strncmp(json.ptr, "{\"Map\":{\"Array\":\"Bytes\"}}", json.len) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);
}

void wirefilter_ffi_ctest_compile_filter() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port == 80")
    );
    rust_assert(result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result.ast != NULL, "could not parse good filter");

    struct wirefilter_compiling_result compiling_result = wirefilter_compile_filter(result.ast);
    rust_assert(compiling_result.status == WIREFILTER_STATUS_SUCCESS, "could not compile filter");
    rust_assert(compiling_result.filter != NULL, "could not compile filter");

    wirefilter_free_compiled_filter(compiling_result.filter);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_create_execution_context() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_add_values_to_execution_context() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    rust_assert(wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        STRING("http.host"),
        BYTES("www.cloudflare.com")
    ) == true, "could not set value for field http.host");

    uint8_t ipv4_addr[4] = {192, 168, 0, 1};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        STRING("ip.src"),
        &ipv4_addr
    ) == true, "could not set value for field ip.src");

    uint8_t ipv6_addr[16] = {20, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    rust_assert(wirefilter_add_ipv6_value_to_execution_context(
        exec_ctx,
        STRING("ip.src"),
        &ipv6_addr
    ) == true, "could not set value for field ip.src");

    rust_assert(wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        STRING("ssl"),
        false
    ) == true, "could not set value for field ssl");

    rust_assert(wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        STRING("tcp.port"),
        80
    ) == true, "could not set value for field tcp.port");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_add_values_to_execution_context_errors() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    rust_assert(wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        STRING("doesnotexist"),
        BYTES("www.cloudflare.com")
    ) == false, "managed to set value for non-existent bytes field");

    uint8_t ipv4_addr[4] = {192, 168, 0, 1};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        STRING("doesnotexist"),
        &ipv4_addr
    ) == false, "managed to set value for non-existent ipv4 field");

    uint8_t ipv6_addr[16] = {20, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    rust_assert(wirefilter_add_ipv6_value_to_execution_context(
        exec_ctx,
        STRING("doesnotexist"),
        &ipv6_addr
    ) == false, "managed to set value for non-existent ipv6 field");

    rust_assert(wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        STRING("doesnotexist"),
        false
    ) == false, "managed to set value for non-existent bool field");

    rust_assert(wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        STRING("doesnotexist"),
        80
    ) == false, "managed to set value for non-existent int field");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_execution_context_serialize() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    rust_assert(wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        STRING("http.host"),
        BYTES("www.cloudflare.com")
    ) == true, "could not set value for field http.host");

    uint8_t ipv4_addr[4] = {192, 168, 0, 1};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        STRING("ip.src"),
        &ipv4_addr
    ) == true, "could not set value for field ip.src");

    // 2606:4700:4700::1111
    uint8_t ipv6_addr[16] = {0x26, 0x06, 0x47, 0x00, 0x47, 0x00, 0, 0, 0, 0, 0, 0, 0, 0, 0x11, 0x11};
    rust_assert(wirefilter_add_ipv6_value_to_execution_context(
        exec_ctx,
        STRING("ip.dst"),
        &ipv6_addr
    ) == true, "could not set value for field ip.src");

    rust_assert(wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        STRING("ssl"),
        false
    ) == true, "could not set value for field ssl");

    rust_assert(wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        STRING("tcp.port"),
        80
    ) == true, "could not set value for field tcp.port");

    struct wirefilter_serializing_result serializing_result = wirefilter_serialize_execution_context_to_json(exec_ctx);
    rust_assert(serializing_result.status == WIREFILTER_STATUS_SUCCESS, "could not serialize execution context to JSON");

    struct wirefilter_rust_allocated_str json = serializing_result.json;
    rust_assert(json.ptr != NULL && json.len > 0, "could not serialize execution context to JSON");

    const char *expected = "{\"http.host\":\"www.cloudflare.com\",\"ip.src\":\"192.168.0.1\",\"ip.dst\":\"2606:4700:4700::1111\",\"ssl\":false,\"tcp.port\":80,\"$lists\":[]}";

    rust_assert(json.len == strlen(expected), "invalid JSON serialization");

    rust_assert(
        strncmp(json.ptr, expected, json.len) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_execution_context_deserialize() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    rust_assert(wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        STRING("http.host"),
        BYTES("www.cloudflare.com")
    ) == true, "could not set value for field http.host");

    struct wirefilter_serializing_result serializing_result = wirefilter_serialize_execution_context_to_json(exec_ctx);
    rust_assert(serializing_result.status == WIREFILTER_STATUS_SUCCESS, "could not serialize execution context to JSON");

    struct wirefilter_rust_allocated_str json = serializing_result.json;
    rust_assert(json.ptr != NULL && json.len > 0, "could not serialize execution context to JSON");

    rust_assert(
        strncmp(json.ptr, "{\"http.host\":\"www.cloudflare.com\",\"$lists\":[]}", json.len) == 0,
        "invalid JSON serialization"
    );

    struct wirefilter_execution_context *conv_exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(conv_exec_ctx != NULL, "could not create execution context");

    bool deserialize_result = wirefilter_deserialize_json_to_execution_context(
        conv_exec_ctx, (unsigned char *)json.ptr, json.len
    );
    rust_assert(deserialize_result == true, "could not deserialize execution context from JSON");

    struct wirefilter_serializing_result conv_serializing_result = wirefilter_serialize_execution_context_to_json(conv_exec_ctx);
    rust_assert(conv_serializing_result.status == WIREFILTER_STATUS_SUCCESS, "could not serialize execution context to JSON");

    struct wirefilter_rust_allocated_str conv_json = conv_serializing_result.json;
    rust_assert(conv_json.ptr != NULL && conv_json.len > 0, "could not serialize execution context to JSON");

    rust_assert(
        strncmp(conv_json.ptr, "{\"http.host\":\"www.cloudflare.com\",\"$lists\":[]}", conv_json.len) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(conv_json);

    wirefilter_free_string(json);

    wirefilter_free_execution_context(conv_exec_ctx);

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}


void wirefilter_ffi_ctest_match_filter() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result = wirefilter_parse_filter(
        scheme,
        STRING("tcp.port == 80")
    );
    rust_assert(result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result.ast != NULL, "could not parse good filter");

    struct wirefilter_compiling_result compiling_result = wirefilter_compile_filter(result.ast);
    rust_assert(compiling_result.status == WIREFILTER_STATUS_SUCCESS, "could not compile filter");
    rust_assert(compiling_result.filter != NULL, "could not compile filter");
    struct wirefilter_filter *filter = compiling_result.filter;

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        STRING("http.host"),
        BYTES("www.cloudflare.com")
    );

    uint8_t ip_addr[4] = {192, 168, 0, 1};
    wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        STRING("ip.src"),
        &ip_addr
    );

    wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        STRING("ssl"),
        false
    );

    wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        STRING("tcp.port"),
        80
    );

    struct wirefilter_matching_result matching_result = wirefilter_match(filter, exec_ctx);
    rust_assert(matching_result.status == WIREFILTER_STATUS_SUCCESS, "could not match filter");

    rust_assert(matching_result.matched == true, "filter should match");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_compiled_filter(filter);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_match_map() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result = wirefilter_parse_filter(
        scheme,
        STRING("http.headers[\"host\"] == \"www.cloudflare.com\"")
    );
    rust_assert(result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result.ast != NULL, "could not parse good filter");

    struct wirefilter_compiling_result compiling_result = wirefilter_compile_filter(result.ast);
    rust_assert(compiling_result.status == WIREFILTER_STATUS_SUCCESS, "could not compile filter");
    rust_assert(compiling_result.filter != NULL, "could not compile filter");
    struct wirefilter_filter *filter = compiling_result.filter;

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        STRING("http.host"),
        BYTES("www.cloudflare.com")
    );

    uint8_t ip_addr[4] = {192, 168, 0, 1};
    wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        STRING("ip.src"),
        &ip_addr
    );

    wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        STRING("ssl"),
        false
    );

    wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        STRING("tcp.port"),
        80
    );

    const char *json = "{\"host\":\"www.cloudflare.com\"}";
    rust_assert(
        wirefilter_add_json_value_to_execution_context(
            exec_ctx,
            STRING("http.headers"),
            BYTES(json)
        ) == true,
        "could not set value for map field http.headers"
    );

    struct wirefilter_matching_result matching_result = wirefilter_match(filter, exec_ctx);
    rust_assert(matching_result.status == WIREFILTER_STATUS_SUCCESS, "could not match filter");

    rust_assert(matching_result.matched == true, "filter should match");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_compiled_filter(filter);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_match_array() {
    struct wirefilter_scheme *scheme = build_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    struct wirefilter_parsing_result result = wirefilter_parse_filter(
        scheme,
        STRING("http.cookies[2] == \"www.cloudflare.com\"")
    );
    rust_assert(result.status == WIREFILTER_STATUS_SUCCESS, "could not parse good filter");
    rust_assert(result.ast != NULL, "could not parse good filter");

    struct wirefilter_compiling_result compiling_result = wirefilter_compile_filter(result.ast);
    rust_assert(compiling_result.status == WIREFILTER_STATUS_SUCCESS, "could not compile filter");
    rust_assert(compiling_result.filter != NULL, "could not compile filter");
    struct wirefilter_filter *filter = compiling_result.filter;

    struct wirefilter_execution_context *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        STRING("http.host"),
        BYTES("www.cloudflare.com")
    );

    uint8_t ip_addr[4] = {192, 168, 0, 1};
    wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        STRING("ip.src"),
        &ip_addr
    );

    wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        STRING("ssl"),
        false
    );

    wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        STRING("tcp.port"),
        80
    );

    const char *json = "[\"one\", \"two\", \"www.cloudflare.com\"]";
    rust_assert(
        wirefilter_add_json_value_to_execution_context(
            exec_ctx,
            STRING("http.cookies"),
            BYTES(json)
        ) == true,
        "could not set value for map field http.cookies"
    );

    struct wirefilter_matching_result matching_result = wirefilter_match(filter, exec_ctx);
    rust_assert(matching_result.status == WIREFILTER_STATUS_SUCCESS, "could not match filter");

    rust_assert(matching_result.matched == true, "filter should match");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_compiled_filter(filter);

    wirefilter_free_scheme(scheme);
}
