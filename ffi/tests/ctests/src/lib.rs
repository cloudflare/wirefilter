use wirefilter_ffi as _;

#[unsafe(no_mangle)]
unsafe extern "C-unwind" fn rust_assert(check: bool, msg: *const std::os::raw::c_char) {
    unsafe {
        assert!(check, "{}", std::ffi::CStr::from_ptr(msg).to_str().unwrap());
    }
}

macro_rules! ffi_ctest {
    (@inner $($name:ident => $link_name:expr,)*) => {
        $(
            #[test]
            #[cfg_attr(miri, ignore)]
            pub fn $name() {
                unsafe extern "C-unwind" {
                    #[link_name = $link_name]
                    fn ctest();
                }

                unsafe { ctest() }
            }
        )*
    };

    ($($name:ident,)*) => {
        ffi_ctest! { @inner
            $($name => concat!("wirefilter_ffi_ctest_", stringify!($name)),)*
        }
    };
}

mod ffi_ctest {
    ffi_ctest!(
        create_array_type,
        create_map_type,
        create_complex_type,
        create_scheme_builder,
        add_fields_to_scheme,
        add_malloced_type_field_to_scheme,
        parse_good_filter,
        parse_bad_filter,
        filter_uses_field,
        filter_uses_list_field,
        filter_hash,
        filter_serialize,
        scheme_serialize,
        type_serialize,
        compile_filter,
        create_execution_context,
        add_values_to_execution_context,
        add_values_to_execution_context_errors,
        execution_context_serialize,
        execution_context_deserialize,
        match_filter,
        match_map,
        match_array,
    );
}
