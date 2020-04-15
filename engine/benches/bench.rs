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

fn bench_large_filter_parse(c: &mut Criterion) {
    let filters = &[
        r#"(http.request.uri.path matches "/up.js|/impl.js|/impl_legacy.js" and http.referer matches "[^a-z\\-]+(earn-url.com|cuturl1.ga|cuturl.ca|antena24.ro|cutsouf.com-transferred|cutearn.ca|cut1.ml|cut1.gq|cut1.ga|cut1.cf|cpm4all.tk|cpm4all.ml|cpm4all.gq|cpm4all.ga|cpm4all.cf|allshort.tk-transferred|allshort.ml-transferred|allshort.gq-transferred|allshort.ga-transferred|allshort.cf-transferred|123short.com|123short.ca|123datingo.com-transferred|emaxsemmy.com|paysnation.com|clubedonude.ga|hotbazeng.com|app-tipps.com|bankfxrates.com|animeplanet.com|wi.cr|howplex.com|pikdo.one|cultivaprofitabil.ro|spotdrama.com|talk49ja.com.ng|luisalfonso89.tk|elscheats.com|younglovepoemsandreviews.blogspot|fourthave.net|nobluffdating.com|mdscript1.gq|hungamaplus.com|soldierlitoshi.xyz|suratmenyurat.net|clinicadematematica.com.br|jobdhundo.online|domain.com|bankfxrates.com|vtube.com.ng|wesyrians.com|klikport.com|blogstart.me|isbufikirbu.com|lasuinfo.com|faucethero.com|crowd24ng.com|siaglobe.com|clinicadematematica.com.br|filmstreamingf.com|w3scholar.com|flaverloaded.com.ng|mjnull.com|addelma.hu|sattaresults.in|healthandhealthyliving.info|dgrafik.net|lypaste.com|countrygames.net|akhirnp.online|lyonkim.com|lyonkim.net|hdmacozetleri.ml|trendingdailyheadlines.com|vetato.com|naijarecruit.com|blogspot.com|vetato.com|jonasl.info|ogfim.ml|bhanu22.ml|newsmee.com|isamultimedia.com|dugifeed.com|mumbleside.com|infoteca.co|izzan.us|jscholarship.com|wrilog.com|discosmx.net|wejoke.online|gnosisoriente.com.ve|fifaworldtv.com|feradsblog.com.ng|gnosisoriente.com.ve|sojworld.com|mkup.us|discosmx.com|igdownloads.com|regularjobs.net|bimsport.net|nhaudzese.com|biggymp3.com|nulled.live|bet9ja.com.ng|uamma.co.uk|anonymousfiles.io|vibethesport.com.ng|life-fitnes.info|worldfreesportsnews.ga|madeboost.tk|barishishab.com|stellarkazan.com|dragonball-saga.tk|szerencsemano.info|0110.tv|omaview.com|domain.com|digissi.com|dkromantik.ru|muhammetkoc.tk|schoolnewsmedia.com|myjobz.net|myjobsnow.com|migrationtips.com|jobsfound.net|dubaijobnet.com|deckinsider.com|careerjourney.net|101insider.com|scouthired.com|sitman123.com|peliculasenmega.com|cooljobagency.com|spor59.com|nashor.cn|your-best-success.com|igtools.net|habertekno.ml|paginadenursing.ro|sitman456.com|sitman345.com|sitman567.com|sitman5678.com|sitman5678.com|sitman345.com|sitman456.com|freebieselect.com|freebieselect.com|stanloaded.net|todaeu.blog.br|sekillinick.net|minersfrenzy.com|thedark.com|rccreature.tech|crispbot.com|hitcanavari.net|awezzome.com|skinnypoints-only.com|nashor.cn|healthyeatingveg.com|blogspot.com|faseberita.id|psfiles.com|bebluntafrica.com|southlandvideos.com|klikport.com|serefkartalim.online|equilibreinfo.com|felloly.com|publicinsta.com|10downloads.com|nossapolitica.net|webdezign.com.br|ultrabuz.com|eartoearmagic.com|extraimage.club|viralvio.com|arlojipro.com|emulatorgamesdownload.com|aniflix.site|cdnstorage.co|wp-ar.net|izlebakalim.net|jumiaphoneprices.com|jobzfree.com|shortpaid.xyz|z2i.com|theeye360.com|theeye360.com|nuitearn.ml|arabweber.com|brust.club|flashfilmes.org|xn--tarihireniyorum-etb11e.com|jelajahcoin.me|pictame.biz|ckk.ai|aykkellin.xyz|jaspersmm.com|filmecrestineonline.ro|mygadgetsinfo.in|domain.com|coshqun.com|idm.com|eksposjabar.com|lemaroc24.com|gistsfanz.com|unitedrental-kw.com|queenfaucet.website|eg4.tech|filmecrestineonline.ro|khazarperfume.com|idm.com|palangagyvai.lt|filmecrestineonline.net|oyuncuplatformu.net|tokvid.com|daysinform.com.ng|mmhighlights.com|crickethighlights.cricket|highlightstore.me|pakistansuperleaguet20.cricket|soccermatchestoday.com|dailylife.com|receivefreesms.net|lordsmobile.org|descargarlordsmobile.com|dolordemuelas.org|dolordeovarios.com|quefuienmividapasada.com|dietapostparto.com|allemoji.com|tarotgratis.pw|salsasparapastas.com|tarotgitano.co|mastitis.net|dolorenlossenos.com|horoscopo.pw|pulpitis.net|curcumalonga.net|duniyanfasaha.guidetricks.com|hanyantsirah.guidetricks.com|abbagana.guidetricks.com|guidetricks.com|gidannovels.guidetricks.com|infopedia24.com)")"#,
    ];

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
                scheme
                    .add_field("http.referer".to_owned(), Type::Bytes)
                    .unwrap();
                scheme
                    .add_field("http.request.uri.path".to_owned(), Type::Bytes)
                    .unwrap();
                move |b: &mut Bencher| {
                    b.iter(|| scheme.parse(filter).unwrap());
                }
            }),
        );
    }
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
        bench_large_filter_parse,
}

criterion_main!(field_benchmarks);
