// https://docs.rs/prometheus-client/latest/prometheus_client/

#[cfg(test)]
mod tests {
    use prometheus_client::encoding::text::encode;
    use prometheus_client::encoding::text::Encode;
    use prometheus_client::metrics::counter::Counter;
    use prometheus_client::metrics::family::Family;
    use prometheus_client::registry::Registry;

    #[derive(Clone, PartialEq, Eq, Hash, Encode)]
    struct Labels {
        method: Method,
        path: String,
    }

    #[derive(Clone, PartialEq, Eq, Hash, Encode)]
    enum Method {
        GET,
        POST,
    }

    #[test]
    fn it_works() {
        let mut registry = <Registry>::default();
        let http_requests = Family::<Labels, Counter>::default();

        registry.register(
            "http_requests",
            "Number of HTTP requests received",
            Box::new(http_requests.clone()),
        );

        let counter = http_requests.get_or_create(&Labels {
            method: Method::GET,
            path: "/metrics".to_string(),
        });
        counter.inc();

        let mut buffer = vec![];
        encode(&mut buffer, &registry).unwrap();

        let expected = "# HELP http_requests Number of HTTP requests received.\n".to_owned()
            + "# TYPE http_requests counter\n"
            + "http_requests_total{method=\"GET\",path=\"/metrics\"} 1\n"
            + "# EOF\n";
        assert_eq!(expected, String::from_utf8(buffer).unwrap());

        for (descriptor, metric) in registry.iter() {
            println!("{}", descriptor.name());
            println!("{:?}", descriptor.labels());
        }
    }
}
