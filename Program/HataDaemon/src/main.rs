#![warn(clippy::all, rust_2018_idioms)]
#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release

mod log_listener;
mod error;

// extern crate alloc;
// use alloc::sync::Arc;

use std::sync::{Arc, Mutex};

// When compiling natively:
#[cfg(not(target_arch = "wasm32"))]
#[tokio::main]
async fn main() {
    // Log to stdout (if you run with `RUST_LOG=debug`).
    tracing_subscriber::fmt::init();

    // // hata init code
    // let current_text: String = "empty".

    let messages = Arc::new(Mutex::new(Vec::new()));

    match log_listener::listen(messages.clone()).await {
        Ok(_) => {}
        Err(e) => println!("Error: {e}")
    }

    let native_options = eframe::NativeOptions::default();
    eframe::run_native(
        "eframe template",
        native_options,
        Box::new(|cc| Box::new(HataDaemon::TemplateApp::new(cc, messages))),
    );

}

// when compiling to web using trunk.
#[cfg(target_arch = "wasm32")]
fn main() {
    // Make sure panics are logged using `console.error`.
    console_error_panic_hook::set_once();

    // Redirect tracing to console.log and friends:
    tracing_wasm::set_as_global_default();

    let web_options = eframe::WebOptions::default();
    eframe::start_web(
        "the_canvas_id", // hardcode it
        web_options,
        Box::new(|cc| Box::new(HataDaemon::TemplateApp::new(cc))),
    )
    .expect("failed to start eframe");
}
