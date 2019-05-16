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
    wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("http.host"),
        WIREFILTER_TYPE_BYTES
    );
    wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("ip.addr"),
        WIREFILTER_TYPE_IP
    );
    wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("ssl"),
        WIREFILTER_TYPE_BOOL
    );
    wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("tcp.port"),
        WIREFILTER_TYPE_INT
    );
    wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("http.headers"),
        wirefilter_create_map_type(WIREFILTER_TYPE_BYTES)
    );
    wirefilter_add_type_field_to_scheme(
        scheme,
        wirefilter_string("http.cookies"),
        wirefilter_create_array_type(WIREFILTER_TYPE_BYTES)
    );
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

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == 80")
    );
    rust_assert(result.success == 1, "could not parse good filter");
    rust_assert(result.ok.ast != NULL, "could not parse good filter");

    rust_assert(
        wirefilter_filter_uses(result.ok.ast, wirefilter_string("tcp.port")) == true,
        "filter should be using field tcp.port"
    );

    rust_assert(
        wirefilter_filter_uses(result.ok.ast, wirefilter_string("ip.addr")) == false,
        "filter should not be using field ip.addr"
    );

    wirefilter_free_parsing_result(result);

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

    uint64_t hash1 = wirefilter_get_filter_hash(result1.ok.ast);

    uint64_t hash2 = wirefilter_get_filter_hash(result2.ok.ast);

    rust_assert(hash1 != 0, "could not compute hash");

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

    wirefilter_rust_allocated_str_t json = wirefilter_serialize_filter_to_json(result.ok.ast);

    rust_assert(json.data != NULL && json.length > 0, "could not serialize filter to JSON");

    rust_assert(
        strncmp(json.data, "{\"lhs\":\"tcp.port\",\"op\":\"Equal\",\"rhs\":80}", json.length) == 0,
        "invalid JSON serialization"
    );

    wirefilter_free_string(json);

    wirefilter_free_parsing_result(result);

    wirefilter_free_scheme(scheme);
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

    wirefilter_filter_t *filter = wirefilter_compile_filter(result.ok.ast);
    rust_assert(filter != NULL, "could not compile filter");

    wirefilter_free_compiled_filter(filter);

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

    wirefilter_filter_t *filter = wirefilter_compile_filter(result.ok.ast);
    rust_assert(filter != NULL, "could not compile filter");

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

    rust_assert(wirefilter_match(filter, exec_ctx) == true, "could not match filter");

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

    wirefilter_filter_t *filter = wirefilter_compile_filter(result.ok.ast);
    rust_assert(filter != NULL, "could not compile filter");

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

    wirefilter_add_bytes_value_to_map(
        http_headers,
        wirefilter_string("host"),
        http_host
    );

    wirefilter_add_map_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.headers"),
        http_headers
    );

    rust_assert(wirefilter_match(filter, exec_ctx) == true, "could not match filter");

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

    wirefilter_filter_t *filter = wirefilter_compile_filter(result.ok.ast);
    rust_assert(filter != NULL, "could not compile filter");

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
    wirefilter_add_bytes_value_to_array(
        http_cookies,
        0,
        http_cookie_one
    );

    wirefilter_externally_allocated_byte_arr_t http_cookie_two;
    http_cookie_two.data = (unsigned char *)"two";
    http_cookie_two.length = strlen((char *)http_cookie_two.data);
    wirefilter_add_bytes_value_to_array(
        http_cookies,
        1,
        http_cookie_two
    );

    wirefilter_add_bytes_value_to_array(
        http_cookies,
        2,
        http_host
    );

    wirefilter_add_array_value_to_execution_context(
        exec_ctx,
        wirefilter_string("http.cookies"),
        http_cookies
    );

    rust_assert(wirefilter_match(filter, exec_ctx) == true, "could not match filter");

    wirefilter_free_execution_context(exec_ctx);

    wirefilter_free_compiled_filter(filter);

    wirefilter_free_scheme(scheme);
}
