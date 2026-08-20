#![feature(rustc_private)]

extern crate rustc_driver;

use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use rustc_driver::{Callbacks, ExternalResourceGuard, ExternalResourceKind};

struct GuardCallbacks {
    observed: Arc<Mutex<Vec<ExternalResourceKind>>>,
}

impl Callbacks for GuardCallbacks {
    fn config(&mut self, config: &mut rustc_driver::CompilerConfig) {
        let observed = Arc::clone(&self.observed);
        config.external_resource_guard = Some(ExternalResourceGuard::new(move |resource_use| {
            assert!(
                !resource_use.span.is_dummy(),
                "external resource observations must retain the source use-site"
            );
            observed
                .lock()
                .expect("external resource observer mutex is poisoned")
                .push(resource_use.kind);
        }));
    }
}

fn main() {
    let mut arguments = std::env::args_os();
    let _program = arguments.next();
    let sysroot = PathBuf::from(arguments.next().expect("missing stage2 sysroot"));
    let source = PathBuf::from(arguments.next().expect("missing input fixture"));
    assert!(arguments.next().is_none(), "unexpected input guard argument");

    let observed = Arc::new(Mutex::new(Vec::new()));
    let mut callbacks = GuardCallbacks {
        observed: Arc::clone(&observed),
    };
    let compiler_arguments = vec![
        "rust-item-dependencies-input-guard".to_owned(),
        source.to_string_lossy().into_owned(),
        "--crate-name=rust_item_dependencies_input_guard".to_owned(),
        "--crate-type=bin".to_owned(),
        "--edition=2024".to_owned(),
        "--emit=metadata=-".to_owned(),
        "--sysroot".to_owned(),
        sysroot.to_string_lossy().into_owned(),
    ];

    let result = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(&compiler_arguments, &mut callbacks)
    });
    assert!(
        result.is_err(),
        "resource-using input must be rejected before analysis"
    );

    let mut observed = observed
        .lock()
        .expect("external resource observer mutex is poisoned")
        .clone();
    observed.sort_by_key(|kind| match kind {
        ExternalResourceKind::Environment => 0,
        ExternalResourceKind::OptionalEnvironment => 1,
    });
    assert_eq!(
        observed,
        [
            ExternalResourceKind::Environment,
            ExternalResourceKind::OptionalEnvironment,
        ]
    );
}
