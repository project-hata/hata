

use egui::widgets::Widget;
use std::sync::{Arc,Mutex};

/// We derive Deserialize/Serialize so we can persist app state on shutdown.
#[derive(serde::Deserialize, serde::Serialize)]
#[serde(default)] // if we add new fields, give them default values when deserializing old state
pub struct TemplateApp {
    // Example stuff:
    label: String,

    // this how you opt-out of serialization of a member
    #[serde(skip)]
    value: f32,

    ///////////////////////// hata ///////////////////////
    current_log: String,
    // myfont: egui::FontId,
    messages: Option<Arc<Mutex<Vec<String>>>>,

}

impl Default for TemplateApp {
    fn default() -> Self {
        Self {
            // Example stuff:
            label: "Hello World!".to_owned(),
            value: 2.7,
            current_log: "".to_owned(),
            messages: None,
            // myfont: egui::FontId::new(10.0, egui::FontFamily::Name(Arc::from("MxFont"))),
        }
    }
}

impl TemplateApp {

    /// Called once before the first frame.
    pub fn new(cc: &eframe::CreationContext<'_>, messages: Arc<Mutex<Vec<String>>>) -> Self {
        setup_custom_fonts(&cc.egui_ctx);

        // This is also where you can customized the look at feel of egui using
        // `cc.egui_ctx.set_visuals` and `cc.egui_ctx.set_fonts`.

        // Load previous app state (if any).
        // Note that you must enable the `persistence` feature for this to work.
        let mut res:Self = Default::default();
        if let Some(storage) = cc.storage {
            res = eframe::get_value(storage, eframe::APP_KEY).unwrap_or_default();
        }
        res.messages = Some(messages);
        res
    }
}

fn setup_custom_fonts(ctx: &egui::Context) {
    // Start with the default fonts (we will be adding to them rather than replacing them).
    let mut fonts = egui::FontDefinitions::default();

    // Install my own font (maybe supporting non-latin characters).
    // .ttf and .otf files supported.
    fonts.font_data.insert(
        "MxFont".to_owned(),
        egui::FontData::from_static(include_bytes!(
            "../assets/MxFontDone.ttf"
        )),
    );

    // // Put my font first (highest priority) for proportional text:
    // fonts
    //     .families
    //     .entry(egui::FontFamily::Proportional)
    //     .or_default()
    //     .insert(0, "MxFont".to_owned());

    // Put my font as last fallback for monospace:
    fonts
        .families
        .entry(egui::FontFamily::Monospace)
        .or_default()
        .insert(0, "MxFont".to_owned());
        // .push("MxFont".to_owned());

    // Tell egui to use these fonts:
    ctx.set_fonts(fonts);
}




impl eframe::App for TemplateApp {
    /// Called by the frame work to save state before shutdown.
    fn save(&mut self, storage: &mut dyn eframe::Storage) {
        eframe::set_value(storage, eframe::APP_KEY, self);
    }

    /// Called each time the UI needs repainting, which may be many times per second.
    /// Put your widgets into a `SidePanel`, `TopPanel`, `CentralPanel`, `Window` or `Area`.
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        // let Self { label, value, current_log } = self;

        egui::CentralPanel::default().show(ctx, |ui| {
            // The central panel the region left after adding TopPanel's and SidePanel's
            let msg = self.messages.clone().unwrap();
            let mut ml = msg.lock().unwrap();

            for s in ml.iter() {
                self.current_log.push_str("\n");
                self.current_log.push_str(s);
            }
            *ml = Vec::new();

            let edit = egui::widgets::TextEdit::multiline(&mut self.current_log)
                .code_editor();
                // .font(self.myfont.clone());

            ui.add_sized(ui.available_size(), edit);
            // let edit_response = edit.ui(ui);
            egui::warn_if_debug_build(ui);
        });

    }
}
