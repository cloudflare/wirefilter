use std::alloc::System;

// Most of our usage will be via FFI as a dynamic library, so we're interested
// in performance with system allocator and not jemalloc.
#[global_allocator]
static A: System = System;

use criterion::{
    criterion_group, criterion_main, Bencher, Benchmark, Criterion, ParameterizedBenchmark,
};
use std::{borrow::Cow, clone::Clone, fmt::Debug, net::IpAddr};
use wirefilter::{
    ExecutionContext, FilterAst, FunctionArgKind, FunctionArgs, GetType, LhsValue, Scheme,
    SimpleFunctionDefinition, SimpleFunctionImpl, SimpleFunctionParam, Type,
};

fn lowercase<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let input = args.next()?.ok()?;
    match input {
        LhsValue::Bytes(mut bytes) => {
            let make_lowercase = match bytes {
                Cow::Borrowed(bytes) => bytes.iter().any(u8::is_ascii_uppercase),
                _ => true,
            };
            if make_lowercase {
                bytes.to_mut().make_ascii_lowercase();
            }
            Some(LhsValue::Bytes(bytes))
        }
        _ => panic!("Invalid type: expected Bytes, got {:?}", input),
    }
}

fn uppercase<'a>(args: FunctionArgs<'_, 'a>) -> Option<LhsValue<'a>> {
    let input = args.next()?.ok()?;
    match input {
        LhsValue::Bytes(mut bytes) => {
            let make_uppercase = match bytes {
                Cow::Borrowed(bytes) => bytes.iter().any(u8::is_ascii_lowercase),
                _ => true,
            };
            if make_uppercase {
                bytes.to_mut().make_ascii_uppercase();
            }
            Some(LhsValue::Bytes(bytes))
        }
        _ => panic!("Invalid type: expected Bytes, got {:?}", input),
    }
}

struct FieldBench<'a, T: 'static> {
    field: &'static str,
    functions: &'a [(&'static str, SimpleFunctionDefinition)],
    filters: &'static [&'static str],
    values: &'a [T],
}

impl<'a, T: 'static + Copy + Debug + Into<LhsValue<'static>>> FieldBench<'a, T> {
    fn run(self, c: &mut Criterion) {
        let FieldBench {
            filters,
            functions,
            field,
            values,
        } = self;

        let ty = values[0].into().get_type();

        for &filter in filters {
            let owned_name;

            // trim ranges because they are usually too long and
            // pollute bench names in HTML and folder names
            let name = if let Some(pos) = filter.find(" in {") {
                owned_name = format!("{} in ...", &filter[..pos]);
                &owned_name
            } else {
                filter
            };

            c.bench(
                "parsing",
                Benchmark::new(name, {
                    let mut scheme = Scheme::default();
                    scheme.add_field(field.to_owned(), ty.clone()).unwrap();
                    for (name, function) in functions {
                        scheme
                            .add_function((*name).into(), function.clone())
                            .unwrap();
                    }
                    move |b: &mut Bencher| {
                        b.iter(|| scheme.parse(filter).unwrap());
                    }
                }),
            );

            c.bench(
                "compilation",
                Benchmark::new(name, {
                    let mut scheme = Scheme::default();
                    scheme.add_field(field.to_owned(), ty.clone()).unwrap();
                    for (name, function) in functions {
                        scheme
                            .add_function((*name).into(), function.clone())
                            .unwrap();
                    }
                    move |b: &mut Bencher| {
                        let filter = scheme.parse(filter).unwrap();

                        b.iter_with_setup(move || filter.clone(), FilterAst::compile);
                    }
                }),
            );

            c.bench(
                "execution",
                ParameterizedBenchmark::new(
                    name,
                    {
                        let mut scheme = Scheme::default();
                        scheme.add_field(field.to_owned(), ty.clone()).unwrap();
                        for (name, function) in functions {
                            scheme
                                .add_function((*name).into(), function.clone())
                                .unwrap();
                        }
                        move |b: &mut Bencher, value: &T| {
                            let filter = scheme.parse(filter).unwrap();

                            let filter = filter.compile();

                            let mut exec_ctx = ExecutionContext::new(&scheme);
                            exec_ctx
                                .set_field_value(scheme.get_field(field).unwrap(), *value)
                                .unwrap();

                            b.iter(|| filter.execute(&exec_ctx));
                        }
                    },
                    values.iter().cloned(),
                ),
            );
        }
    }
}

fn bench_ip_comparisons(c: &mut Criterion) {
    FieldBench {
        field: "ip.addr",
        functions: &[],
        filters: &[
            "ip.addr == 173.245.48.1",
            "ip.addr == 2606:4700:4700::1111",
            "ip.addr >= 173.245.48.0 && ip.addr < 173.245.49.0",
            "ip.addr >= 2606:4700:: && ip.addr < 2606:4701::",
            "ip.addr in { 103.21.244.0/22 2405:8100::/32 104.16.0.0/12 2803:f800::/32 131.0.72.0/22 173.245.48.0/20 2405:b500::/32 172.64.0.0/13 190.93.240.0/20 103.22.200.0/22 2606:4700::/32 198.41.128.0/17 197.234.240.0/22 162.158.0.0/15 108.162.192.0/18 2c0f:f248::/32 2400:cb00::/32 103.31.4.0/22 2a06:98c0::/29 141.101.64.0/18 188.114.96.0/20 }"
        ],
        values: &[
            IpAddr::from([127, 0, 0, 1]),
            IpAddr::from([0x2001, 0x0db8, 0x85a3, 0x0000, 0x0000, 0x8a2e, 0x0370, 0x7334]),
            IpAddr::from([173, 245, 48, 1]),
            IpAddr::from([0x2606, 0x4700, 0x4700, 0x0000, 0x0000, 0x0000, 0x0000, 0x1111]),
        ]
    }.run(c)
}

fn bench_int_comparisons(c: &mut Criterion) {
    FieldBench {
        field: "tcp.port",
        functions: &[],
        filters: &[
            "tcp.port == 80",
            "tcp.port >= 1024",
            "tcp.port in { 80 8080 8880 2052 2082 2086 2095 }",
        ],
        values: &[80, 8081],
    }
    .run(c)
}

fn bench_string_comparisons(c: &mut Criterion) {
    FieldBench {
        field: "ip.geoip.country",
        functions: &[],
        filters: &[
            r#"ip.geoip.country == "GB""#,
            r#"ip.geoip.country in { "AT" "BE" "BG" "HR" "CY" "CZ" "DK" "EE" "FI" "FR" "DE" "GR" "HU" "IE" "IT" "LV" "LT" "LU" "MT" "NL" "PL" "PT" "RO" "SK" "SI" "ES" "SE" "GB" "GF" "GP" "MQ" "ME" "YT" "RE" "MF" "GI" "AX" "PM" "GL" "BL" "SX" "AW" "CW" "WF" "PF" "NC" "TF" "AI" "BM" "IO" "VG" "KY" "FK" "MS" "PN" "SH" "GS" "TC" "AD" "LI" "MC" "SM" "VA" "JE" "GG" "GI" "CH" }"#,
        ],
        values: &["GB", "T1"],
    }.run(c)
}

fn bench_string_matches(c: &mut Criterion) {
    FieldBench {
        field: "http.user_agent",
        functions: &[],
        filters: &[
            r#"http.user_agent ~ "(?i)googlebot/\d+\.\d+""#,
            r#"http.user_agent ~ "Googlebot""#,
            r#"http.user_agent contains "Googlebot""#
        ],
        values: &[
            "Mozilla/5.0 AppleWebKit/537.36 (KHTML, like Gecko; compatible; Googlebot/2.1; +http://www.google.com/bot.html) Safari/537.36",
            "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/51.0.2704.103 Safari/537.36"
        ]
    }.run(c)
}

fn bench_string_function_comparison(c: &mut Criterion) {
    FieldBench {
        field: "http.host",
        functions: &[
            (
                "lowercase",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: vec![],
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(lowercase),
                },
            ),
            (
                "uppercase",
                SimpleFunctionDefinition {
                    params: vec![SimpleFunctionParam {
                        arg_kind: FunctionArgKind::Field,
                        val_type: Type::Bytes,
                    }],
                    opt_params: vec![],
                    return_type: Type::Bytes,
                    implementation: SimpleFunctionImpl::new(uppercase),
                },
            ),
        ],
        filters: &[
            r#"lowercase(http.host) == "example.org""#,
            r#"uppercase(lowercase(http.host)) == "EXAMPLE.ORG""#,
        ],
        values: &["example.org", "EXAMPLE.ORG"],
    }
    .run(c)
}

criterion_group! {
    name = field_benchmarks;
    config = Criterion::default();
    targets =
        bench_ip_comparisons,
        bench_int_comparisons,
        bench_string_comparisons,
        bench_string_matches,
        bench_string_function_comparison,
}

criterion_main!(field_benchmarks);
