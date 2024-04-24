pub use authentication::*;
pub use build_options::*;
pub use config_settings::*;
pub use constraints::*;
pub use name_specifiers::*;
pub use overrides::*;
pub use package_options::*;
use pep508_rs::VerbatimUrl;
pub use preview::*;
pub use target_triple::*;

type Requirement = pep508_rs::Requirement<VerbatimUrl>;

mod authentication;
mod build_options;
mod config_settings;
mod constraints;
mod name_specifiers;
mod overrides;
mod package_options;
mod preview;
mod target_triple;
