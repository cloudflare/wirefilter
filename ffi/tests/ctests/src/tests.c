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

void wirefilter_ffi_ctest_create_scheme() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");
    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_add_fields_to_scheme() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

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

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_parse_good_filter() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

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

    wirefilter_parsing_result_t result = wirefilter_parse_filter(
        scheme,
        wirefilter_string("tcp.port == \"wirefilter\"")
    );
    rust_assert(result.success == false, "should not parse bad filter");
    rust_assert(result.err.msg.data && result.err.msg.length > 0, "missing error message");

    wirefilter_free_parsing_result(result);

    wirefilter_free_scheme(scheme);
}

void wirefilter_ffi_ctest_compile_filter() {
    wirefilter_scheme_t *scheme = wirefilter_create_scheme();
    rust_assert(scheme != NULL, "could not create scheme");

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
