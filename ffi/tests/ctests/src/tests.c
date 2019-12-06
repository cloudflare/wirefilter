#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include <wirefilter.h>

extern void rust_assert(bool check, const char *msg);

static wirefilter_externally_allocated_str_t wirefilter_string(const char *s) {
    wirefilter_externally_allocated_str_t str;
    str.data = s;
    str.length = strlen(s);
    return str;
}

void initialize_scheme(wirefilter_scheme_t *scheme) {
    rust_assert(wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("http.host"),
        WIREFILTER_TYPE_BYTES
    ), "could not add field http.host of type \"Bytes\" to scheme");
    rust_assert(wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("ip.addr"),
        WIREFILTER_TYPE_IP
    ), "could not add field ip.addr of type \"Ip\" to scheme");
    rust_assert(wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("ssl"),
        WIREFILTER_TYPE_BOOL
    ), "could not add field ssl of type \"Bool\" to scheme");
    rust_assert(wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("tcp.port"),
        WIREFILTER_TYPE_INT
    ), "could not add field tcp.port of type \"Int\" to scheme");
    wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("http.headers"),
        wirefilter_create_map_type(WIREFILTER_TYPE_BYTES)
    );
    rust_assert(wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("http.cookies"),
        wirefilter_create_array_type(WIREFILTER_TYPE_BYTES)
    ), "could not add field http.cookies of type \"Array<Bytes>\" to scheme");
}

void wirefilter_ffi_ctest_create_array_type() {
    wirefilter_type_t array_type = wirefilter_create_array_type(WIREFILTER_TYPE_BYTES);
    rust_assert(array_type.tag == WIREFILTER_TYPE_TAG_ARRAY, "could not create valid array type");
}

void wirefilter_ffi_ctest_create_map_type() {
    wirefilter_type_t map_type = wirefilter_create_map_type(WIREFILTER_TYPE_BYTES);
    rust_assert(map_type.tag == WIREFILTER_TYPE_TAG_MAP, "could not create valid map type");
}

void wirefilter_ffi_ctest_create_scheme() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");
    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_add_fields_to_scheme() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_add_malloced_type_field_to_scheme() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    wirefilter_type_t *byte_type = (wirefilter_type_t *)malloc(sizeof(wirefilter_type_t));
    rust_assert(byte_type != NULL, "could not allocate type");
    *byte_type = WIREFILTER_TYPE_BYTES;

    rust_assert(wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("http.host"),
        *byte_type
    ), "could not add field http.host of type \"Bytes\" to scheme");

    free(byte_type);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_parse_good_filter() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == 80")
    );
    rust_assert(result.success == 1, "could not parse good filter");
    rust_assert(result.ok.ast != NULL, "could not parse good filter");

    wirefilter_free_parsing_result(result);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_parse_bad_filter() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == \"wirefilter\"")
    );
    rust_assert(result.success == false, "should not parse bad filter");
    rust_assert(result.err.msg.data && result.err.msg.length > 0, "missing error message");

    wirefilter_free_parsing_result(result);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_filter_uses_field() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t parsing_result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == 80")
    );
    rust_assert(parsing_result.success == 1, "could not parse good filter");
    rust_assert(parsing_result.ok.ast != NULL, "could not parse good filter");

    wirefilter_using_result_t using_result;

    using_result = wirefilter_filter_uses(
        parsing_result.ok.ast,
        wirefilter_string("tcp.port")
    );

    rust_assert(using_result.success == 1, "could not check if filter uses tcp.port field");
    rust_assert(using_result.ok.value == true, "filter should be using field tcp.port");

    using_result = wirefilter_filter_uses(
        parsing_result.ok.ast,
        wirefilter_string("ip.addr")
    );

    rust_assert(using_result.success == 1, "could not check if filter uses ip.addr field");
    rust_assert(using_result.ok.value == false, "filter should not be using field ip.addr");

    wirefilter_free_parsing_result(parsing_result);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_filter_hash() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result1 = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == 80")
    );
    rust_assert(result1.success == 1, "could not parse good filter");
    rust_assert(result1.ok.ast != NULL, "could not parse good filter");

    wirefilter_parsing_result_t result2 = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port              ==80")
    );
    rust_assert(result2.success == 1, "could not parse good filter");
    rust_assert(result2.ok.ast != NULL, "could not parse good filter");

    wirefilter_hashing_result_t hashing_result;

    hashing_result = wirefilter_get_filter_hash(result1.ok.ast);
    rust_assert(hashing_result.success == 1, "could not compute hash");
    uint64_t hash1 = hashing_result.ok.hash;

    hashing_result = wirefilter_get_filter_hash(result2.ok.ast);
    rust_assert(hashing_result.success == 1, "could not compute hash");
    uint64_t hash2 = hashing_result.ok.hash;

    rust_assert(hash1 == hash2, "both filters should have the same hash");

    wirefilter_free_parsing_result(result1);

    wirefilter_free_parsing_result(result2);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_filter_serialize() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == 80")
    );
    rust_assert(result.success == 1, "could not parse good filter");
    rust_assert(result.ok.ast != NULL, "could not parse good filter");

    wirefilter_serializing_result_t serializing_result = wirefilter_serialize_filter_to_json(result.ok.ast);
    rust_assert(serializing_result.success == 1, "could not serialize filter to JSON");

    wirefilter_rust_allocated_str_t json = serializing_result.ok.json;
    rust_assert(json.data != NULL && json.length > 0, "could not serialize filter to JSON");

    rust_assert(
        strncmp(json.data, "{\"lhs\":\"tcp.port\",\"op\":\"Equal\",\"rhs\":80}", json.length) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_free_parsing_result(result);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_scheme_serialize() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_serializing_result_t serializing_result = wirefilter_serialize_scheme_to_json(scheme);
    rust_assert(serializing_result.success == 1, "could not serialize scheme to JSON");

    wirefilter_rust_allocated_str_t json = serializing_result.ok.json;
    rust_assert(json.data != NULL && json.length > 0, "could not serialize scheme to JSON");

    rust_assert(
        strncmp(json.data, "{\"http.host\":\"Bytes\",\"ip.addr\":\"Ip\",\"ssl\":\"Bool\",\"tcp.port\":\"Int\",\"http.headers\":{\"Map\":\"Bytes\"},\"http.cookies\":{\"Array\":\"Bytes\"}}", json.length) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_type_serialize() {
    wirefilter_serializing_result_t serializing_result = wirefilter_serialize_type_to_json(&WIREFILTER_TYPE_BYTES);
    rust_assert(serializing_result.success == 1, "could not serialize type to JSON");

    wirefilter_rust_allocated_str_t json = serializing_result.ok.json;
    rust_assert(json.data != NULL && json.length > 0, "could not serialize type to JSON");

    rust_assert(
        strncmp(json.data, "\"Bytes\"", json.length) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_type_t type = wirefilter_create_map_type(
        wirefilter_create_array_type(WIREFILTER_TYPE_BYTES)
    );

    serializing_result = wirefilter_serialize_type_to_json(&type);
    rust_assert(serializing_result.success == 1, "could not serialize type to JSON");

    json = serializing_result.ok.json;
    rust_assert(json.data != NULL && json.length > 0, "could not serialize type to JSON");

    rust_assert(
        strncmp(json.data, "{\"Map\":{\"Array\":\"Bytes\"}}", json.length) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);
}

void wirefilter_ffi_ctest_compile_filter() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == 80")
    );
    rust_assert(result.success == true, "could not parse good filter");
    rust_assert(result.ok.ast != NULL, "could not parse good filter");

    wirefilter_compiling_result_t compiling_result = wirefilter_compile_filter(result.ok.ast);
    rust_assert(compiling_result.success == true, "could not compile filter");
    rust_assert(compiling_result.ok.filter != NULL, "could not compile filter");

    wirefilter_free_compiled_filter(compiling_result.ok.filter);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_create_execution_context() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    wirefilter_execution_context_t *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_add_values_to_execution_context() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_execution_context_t *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_externally_allocated_byte_arr_t http_host;
    http_host.data = (unsigned char *)"www.cloudflare.com";
    http_host.length = strlen((char *)http_host.data);
    rust_assert(wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.host"),
        http_host
    ) == true, "could not set value for field http.host");

    uint8_t ipv4_addr[4] = {192, 168, 0, 1};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ip.addr"),
        ipv4_addr
    ) == true, "could not set value for field ip.addr");

    uint8_t ipv6_addr[16] = {20, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ip.addr"),
        ipv6_addr
    ) == true, "could not set value for field ip.addr");

    rust_assert(wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ssl"),
        false
    ) == true, "could not set value for field ssl");

    rust_assert(wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        wirefilter_string("tcp.port"),
        80
    ) == true, "could not set value for field tcp.port");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_add_values_to_execution_context_errors() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_execution_context_t *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_externally_allocated_byte_arr_t http_host;
    http_host.data = (unsigned char *)"www.cloudflare.com";
    http_host.length = strlen((char *)http_host.data);
    rust_assert(wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        wirefilter_string("doesnotexist"),
        http_host
    ) == false, "managed to set value for non-existent bytes field");

    uint8_t ipv4_addr[4] = {192, 168, 0, 1};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("doesnotexist"),
        ipv4_addr
    ) == false, "managed to set value for non-existent ipv4 field");

    uint8_t ipv6_addr[16] = {20, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    rust_assert(wirefilter_add_ipv6_value_to_execution_context(
        exec_ctx,
        wirefilter_string("doesnotexist"),
        ipv6_addr
    ) == false, "managed to set value for non-existent ipv6 field");

    rust_assert(wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        wirefilter_string("doesnotexist"),
        false
    ) == false, "managed to set value for non-existent bool field");

    rust_assert(wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        wirefilter_string("doesnotexist"),
        80
    ) == false, "managed to set value for non-existent int field");

    wirefilter_map_t *more_http_headers = wirefilter_create_map(
        WIREFILTER_TYPE_BYTES
    );
    rust_assert(wirefilter_add_map_value_to_execution_context(
        exec_ctx,
        wirefilter_string("doesnotexist"),
        more_http_headers
    ) == false, "managed to set value for non-existent map field");

    wirefilter_array_t *http_cookies = wirefilter_create_array(
        WIREFILTER_TYPE_BYTES
    );
    rust_assert(wirefilter_add_array_value_to_execution_context(
        exec_ctx,
        wirefilter_string("doesnotexist"),
        http_cookies
    ) == false, "managed to set value for non-existent array field");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_execution_context_serialize() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_execution_context_t *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_externally_allocated_byte_arr_t http_host;
    http_host.data = (unsigned char *)"www.cloudflare.com";
    http_host.length = strlen((char *)http_host.data);
    rust_assert(wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.host"),
        http_host
    ) == true, "could not set value for field http.host");

    uint8_t ipv4_addr[4] = {192, 168, 0, 1};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ip.addr"),
        ipv4_addr
    ) == true, "could not set value for field ip.addr");

    uint8_t ipv6_addr[16] = {20, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    rust_assert(wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ip.addr"),
        ipv6_addr
    ) == true, "could not set value for field ip.addr");

    rust_assert(wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ssl"),
        false
    ) == true, "could not set value for field ssl");

    rust_assert(wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        wirefilter_string("tcp.port"),
        80
    ) == true, "could not set value for field tcp.port");

    wirefilter_serializing_result_t serializing_result = wirefilter_serialize_execution_context_to_json(exec_ctx);
    rust_assert(serializing_result.success == 1, "could not serialize execution context to JSON");

    wirefilter_rust_allocated_str_t json = serializing_result.ok.json;
    rust_assert(json.data != NULL && json.length > 0, "could not serialize execution context to JSON");

    rust_assert(
        strncmp(json.data, "{\"http.host\":\"www.cloudflare.com\",\"ip.addr\":\"20.20.0.0\",\"ssl\":false,\"tcp.port\":80}", json.length) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_scheme(scheme);
}


void wirefilter_ffi_ctest_match_filter() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == 80")
    );
    rust_assert(result.success == true, "could not parse good filter");
    rust_assert(result.ok.ast != NULL, "could not parse good filter");

    wirefilter_compiling_result_t compiling_result = wirefilter_compile_filter(result.ok.ast);
    rust_assert(compiling_result.success == true, "could not compile filter");
    rust_assert(compiling_result.ok.filter != NULL, "could not compile filter");
    wirefilter_filter_t *filter = compiling_result.ok.filter;

    wirefilter_execution_context_t *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_externally_allocated_byte_arr_t http_host;
    http_host.data = (unsigned char *)"www.cloudflare.com";
    http_host.length = strlen((char *)http_host.data);
    wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.host"),
        http_host
    );

    uint8_t ip_addr[4] = {192, 168, 0, 1};
    wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ip.addr"),
        ip_addr
    );

    wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ssl"),
        false
    );

    wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        wirefilter_string("tcp.port"),
        80
    );

    wirefilter_matching_result_t matching_result = wirefilter_match(filter, exec_ctx);
    rust_assert(matching_result.success == 1, "could not match filter");

    rust_assert(matching_result.ok.value == true, "filter should match");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_compiled_filter(filter);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_match_map() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("http.headers[\"host\"] == \"www.cloudflare.com\"")
    );
    rust_assert(result.success == true, "could not parse good filter");
    rust_assert(result.ok.ast != NULL, "could not parse good filter");

    wirefilter_compiling_result_t compiling_result = wirefilter_compile_filter(result.ok.ast);
    rust_assert(compiling_result.success == true, "could not compile filter");
    rust_assert(compiling_result.ok.filter != NULL, "could not compile filter");
    wirefilter_filter_t *filter = compiling_result.ok.filter;

    wirefilter_execution_context_t *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_externally_allocated_byte_arr_t http_host;
    http_host.data = (unsigned char *)"www.cloudflare.com";
    http_host.length = strlen((char *)http_host.data);
    wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.host"),
        http_host
    );

    uint8_t ip_addr[4] = {192, 168, 0, 1};
    wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ip.addr"),
        ip_addr
    );

    wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ssl"),
        false
    );

    wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        wirefilter_string("tcp.port"),
        80
    );

    wirefilter_map_t *http_headers = wirefilter_create_map(
        WIREFILTER_TYPE_BYTES
    );

    rust_assert(wirefilter_add_bytes_value_to_map(
        http_headers,
        wirefilter_string("host"),
        http_host
    ), "could not add bytes value to map");

    rust_assert(wirefilter_add_map_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.headers"),
        http_headers
    ) == true, "could not set value for map field http.headers");

    wirefilter_matching_result_t matching_result = wirefilter_match(filter, exec_ctx);
    rust_assert(matching_result.success == 1, "could not match filter");

    rust_assert(matching_result.ok.value == true, "filter should match");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_compiled_filter(filter);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_match_array() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

    initialize_scheme(scheme);

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("http.cookies[2] == \"www.cloudflare.com\"")
    );
    rust_assert(result.success == true, "could not parse good filter");
    rust_assert(result.ok.ast != NULL, "could not parse good filter");

    wirefilter_compiling_result_t compiling_result = wirefilter_compile_filter(result.ok.ast);
    rust_assert(compiling_result.success == true, "could not compile filter");
    rust_assert(compiling_result.ok.filter != NULL, "could not compile filter");
    wirefilter_filter_t *filter = compiling_result.ok.filter;

    wirefilter_execution_context_t *exec_ctx = wirefilter_create_execution_context(scheme);
    rust_assert(exec_ctx != NULL, "could not create execution context");

    wirefilter_externally_allocated_byte_arr_t http_host;
    http_host.data = (unsigned char *)"www.cloudflare.com";
    http_host.length = strlen((char *)http_host.data);
    wirefilter_add_bytes_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.host"),
        http_host
    );

    uint8_t ip_addr[4] = {192, 168, 0, 1};
    wirefilter_add_ipv4_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ip.addr"),
        ip_addr
    );

    wirefilter_add_bool_value_to_execution_context(
        exec_ctx,
        wirefilter_string("ssl"),
        false
    );

    wirefilter_add_int_value_to_execution_context(
        exec_ctx,
        wirefilter_string("tcp.port"),
        80
    );

    wirefilter_array_t *http_cookies = wirefilter_create_array(
        WIREFILTER_TYPE_BYTES
    );

    wirefilter_externally_allocated_byte_arr_t http_cookie_one;
    http_cookie_one.data = (unsigned char *)"one";
    http_cookie_one.length = strlen((char *)http_cookie_one.data);
    rust_assert(wirefilter_add_bytes_value_to_array(
        http_cookies,
        0,
        http_cookie_one
    ), "could not add bytes value to array");

    wirefilter_externally_allocated_byte_arr_t http_cookie_two;
    http_cookie_two.data = (unsigned char *)"two";
    http_cookie_two.length = strlen((char *)http_cookie_two.data);
    rust_assert(wirefilter_add_bytes_value_to_array(
        http_cookies,
        1,
        http_cookie_two
    ), "could not add bytes value to array");

    rust_assert(wirefilter_add_bytes_value_to_array(
        http_cookies,
        2,
        http_host
    ), "could not add bytes value to array");

    rust_assert(wirefilter_add_array_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.cookies"),
        http_cookies
    ) == true, "could not set value for map field http.cookies");

    wirefilter_matching_result_t matching_result = wirefilter_match(filter, exec_ctx);
    rust_assert(matching_result.success == 1, "could not match filter");

    rust_assert(matching_result.ok.value == true, "filter should match");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_compiled_filter(filter);

    wirefilter_free_scheme(scheme);
}
