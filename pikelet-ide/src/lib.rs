use log::info;
use lsp_server::{Connection, Message};
use lsp_types::{InitializeParams, ServerCapabilities};
use std::error::Error;

pub fn run() -> Result<(), Box<dyn Error>> {
    // Set up logging. Because `stdio_transport` gets a lock on stdout and stdin, we must have
    // our logging only write out to stderr.
    flexi_logger::Logger::with_str("info").start().unwrap();
    info!("Starting Pikelet LSP server");

    // Create the transport. Includes the stdio (stdin and stdout) versions but this could
    // also be implemented to use sockets or HTTP.
    let (connection, io_threads) = Connection::stdio();

    // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
    let server_capabilities = serde_json::to_value(&ServerCapabilities::default()).unwrap();
    let initialization_params = connection.initialize(server_capabilities)?;
    main_loop(&connection, initialization_params)?;
    io_threads.join()?;

    // Shut down gracefully.
    info!("Shutting down server");

    Ok(())
}

fn main_loop(connection: &Connection, params: serde_json::Value) -> Result<(), Box<dyn Error>> {
    let _params: InitializeParams = serde_json::from_value(params).unwrap();

    info!("Starting Pikelet main loop");
    for msg in &connection.receiver {
        info!("Received msg: {:?}", msg);
        match msg {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    return Ok(());
                }
                info!("Got request: {:?}", request);
            }
            Message::Response(response) => {
                info!("Received response: {:?}", response);
            }
            Message::Notification(notification) => {
                info!("Received notification: {:?}", notification);
            }
        }
    }

    Ok(())
}
