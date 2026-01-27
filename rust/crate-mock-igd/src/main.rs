use mock_igd::{Action, MockIgdServer, Protocol, Responder};

#[tokio::main]
async fn main() {
    // Start the mock IGD server
    let server = MockIgdServer::start().await.unwrap();

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
                .with_external_port(8080)
                .with_protocol(Protocol::TCP),
            Responder::success(),
        )
        .await;

    server
        .mock(
            Action::add_port_mapping().with_external_port(80),
            Responder::error(718, "ConflictInMappingEntry"),
        )
        .await;

    println!("Server is running. Press Ctrl+C to stop.");

    // Wait for Ctrl+C to keep the server running
    tokio::signal::ctrl_c()
        .await
        .expect("Failed to listen for Ctrl+C");

    println!("Shutting down...");
}
