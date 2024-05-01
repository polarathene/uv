//! Find matching Python interpreter and query information about python interpreter.
//!
//! * The `venv` subcommand uses [`find_requested_python`] if `-p`/`--python` is used and
//!   `find_default_python` otherwise.
//! * The `compile` subcommand uses [`find_best_python`].
//! * The `sync`, `install`, `uninstall`, `freeze`, `list` and `show` subcommands use
//!   [`find_default_python`] when `--python` is used, [`find_default_python`] when `--system` is used
//!   and the current venv by default.

use std::ffi::OsString;
use std::io;

use thiserror::Error;

pub use crate::discovery::Error as DiscoveryError;
pub use crate::environment::PythonEnvironment;
pub use crate::find_python::{find_best_python, find_default_python, find_requested_python};
pub use crate::interpreter::Interpreter;
pub use crate::python_version::PythonVersion;
pub use crate::target::Target;
pub use crate::virtualenv::{Error as VirtualEnvError, PyVenvConfiguration, VirtualEnvironment};

mod discovery;
mod environment;
mod find_python;
mod implementation;
mod interpreter;
pub mod managed;
pub mod platform;
mod py_launcher;
mod python_version;
mod target;
mod virtualenv;

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    VirtualEnv(#[from] virtualenv::Error),

    #[error(transparent)]
    Query(#[from] interpreter::Error),

    #[error(transparent)]
    Request(#[from] discovery::Error),

    #[error(transparent)]
    PyLauncher(#[from] py_launcher::Error),

    #[error("No versions of Python could be found. Is Python installed?")]
    PythonNotFound,
    #[error("Failed to locate a virtualenv or Conda environment (checked: `VIRTUAL_ENV`, `CONDA_PREFIX`, and `.venv`). Run `uv venv` to create a virtualenv.")]
    VenvNotFound,
    #[error("Failed to locate Python interpreter at `{0}`")]
    RequestedPythonNotFound(String),
    #[error(transparent)]
    Io(#[from] io::Error),
    #[cfg(windows)]
    #[error(
        "No Python {0} found through `py --list-paths` or in `PATH`. Is Python {0} installed?"
    )]
    NoSuchPython(String),
    #[cfg(unix)]
    #[error("No Python {0} in `PATH`. Is Python {0} installed?")]
    NoSuchPython(String),
    #[error("Neither `python` nor `python3` are in `PATH`. Is Python installed?")]
    NoPythonInstalledUnix,
    #[error(
        "Could not find `python.exe` through `py --list-paths` or in 'PATH'. Is Python installed?"
    )]
    NoPythonInstalledWindows,
    #[error("Failed to write to cache")]
    Encode(#[from] rmp_serde::encode::Error),
    #[error("Error finding `{}` in PATH", _0.to_string_lossy())]
    WhichError(OsString, #[source] which::Error),
}
