use tracing::{instrument, warn};
use opentelemetry::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use tracing_opentelemetry::OpenTelemetryLayer;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt, Layer};

// cd sandbox/grafana-tempo
// docker compose up
// open http://localhost:3000
//    -> admin/admin

// TraceQL
// {}
// { resource.service.name = "service_name_sandbox"}


pub fn init_telemetry() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {

    let exporter = opentelemetry_otlp::SpanExporter::builder()
        .with_tonic()
        .with_endpoint("http://127.0.0.1:4317")
        .build()
        .map_err(|e| format!("Failed to create OTLP exporter: {:?}", e))?;

    let provider = opentelemetry_sdk::trace::SdkTracerProvider::builder()
        .with_batch_exporter(exporter)
        .with_resource(
            opentelemetry_sdk::Resource::builder()
                .with_service_name("service_name_sandbox")
                .build(),
        )
        .build();

    let tracer = provider.tracer("tracer_name_sandbox");
    let otlp_layer = OpenTelemetryLayer::new(tracer).boxed();
    let fmt_layer = tracing_subscriber::fmt::layer().with_filter(tracing_subscriber::EnvFilter::try_new("debug").unwrap()).boxed();
    let layers = vec![otlp_layer, fmt_layer];

    tracing_subscriber::registry()
        .with(layers)
        .init();

    Ok(())
}

#[instrument(level = "trace")]
pub fn add(left: u64, right: u64) -> u64 {
    warn!("Adding {} + {}", left, right);
    println!("Adding {} + {}", left, right);
    left + right
}

#[cfg(test)]
mod tests {
    use std::time::Duration;
    use super::*;

    #[tokio::test]
    async fn it_works() {

        init_telemetry().expect("Failed to initialize telemetry");

        let mut attempts = 0;
        while attempts < 10 {
            tokio::time::sleep(Duration::from_millis(1000)).await;
            let _ = add(2, 2);
            attempts += 1;
        }

        println!("Done");
    }
}
