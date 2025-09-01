use tracing::{info, instrument};
use opentelemetry::trace::TracerProvider;
use opentelemetry_otlp::WithExportConfig;
use tracing_opentelemetry::OpenTelemetryLayer;
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

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
        .with_endpoint("http://localhost:4317")
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

    tracing_subscriber::registry()
        .with(OpenTelemetryLayer::new(tracer))
        .init();

    Ok(())
}

#[instrument]
pub fn add(left: u64, right: u64) -> u64 {
    info!("Adding {} + {}", left, right);
    println!("Adding {} + {}", left, right);
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn it_works() {
        init_telemetry().expect("Failed to initialize telemetry");
        let result = add(2, 2);
        assert_eq!(result, 4);
        let result = add(3, 3);
        assert_eq!(result, 6);

        // Give some time for traces to be exported
        tokio::time::sleep(std::time::Duration::from_millis(500)).await;
        println!("Done");
    }
}
