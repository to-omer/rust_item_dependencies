use serde::{Deserialize, Serialize};

pub const RESULT_ARGUMENT: &str = "--rust-item-dependencies-container-result";
pub const RESULT_PATH: &str = "/tmp/rid-output/result.json";
pub const VERSION: u32 = 1;

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ContainerResult {
    pub version: u32,
    pub input: String,
    pub output: Option<String>,
    pub original: String,
    pub reduced: String,
}
