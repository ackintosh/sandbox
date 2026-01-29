use mock_igd::{Action, MockIgdServer, Protocol, Responder};

#[tokio::main]
async fn main() {
    let _ = tracing_subscriber::fmt::try_init();
    tracing::info!("Hello, mock-igd!");

    // Start the mock IGD server
    let server = MockIgdServer::builder()
        // Enable SSDP
        .with_ssdp()
        .start().await.unwrap();

    println!("Mock IGD server started!");
    println!("  Root URL: {}", server.url());
    println!("  Control URL: {}", server.control_url());
    println!();

    // Register mock behaviors
    server
        .mock(
            Action::GetExternalIPAddress,
            Responder::success().with_external_ip("203.0.113.42".parse().unwrap()),
        )
        .await;

    server
        .mock(
            Action::add_port_mapping()
                // .with_external_port(8080)
                .with_protocol(Protocol::TCP),
            Responder::success(),
        )
        .await;

    // server
    //     .mock(
    //         Action::add_port_mapping().with_external_port(80),
    //         Responder::error(718, "ConflictInMappingEntry"),
    //     )
    //     .await;

    // server.mock(
    //     Action::GetStatusInfo,
    //     Responder::success()
    //         .with_connection_status("Connected")
    //         .with_last_connection_error("ERROR_NONE")
    //         .with_uptime(86400)  // 1日 = 86400秒
    // ).await;

    println!("Server is running. Press Ctrl+C to stop.");

    // Wait for Ctrl+C to keep the server running
    tokio::signal::ctrl_c()
        .await
        .expect("Failed to listen for Ctrl+C");

    println!();
    println!("Received SSDP Requests:");
    for req in server.received_ssdp_requests().await.iter() {
        println!("-------------------------------------------------------------");
        println!("source: {:?}", req.source);
        println!("search_target (ST header value): {:?}", req.search_target);
        println!("MAN header value: {:?}", req.man);
        println!("MX header value (maximum wait time in seconds): {:?}", req.mx);
    }
    println!("-------------------------------------------------------------");

    println!();
    println!("Received Requests:");
    for req in server.received_requests().await.iter() {
        println!("-------------------------------------------------------------");
        println!("action_name: {:?}", req.action_name);
        println!("service_type: {:?}", req.service_type);
        println!("body: {:?}", req.body);
        println!("timestamp: {:?}", req.timestamp);
    }
    println!("-------------------------------------------------------------");
    println!("Shutting down...");
    server.shutdown();
}
