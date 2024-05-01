use std::collections::HashSet;
use std::env;

use tracing::{debug, instrument, warn};

use uv_cache::Cache;
use uv_warnings::warn_user_once;

use crate::discovery::{
    find_interpreter, Error as DiscoveryError, FindResult, InterpreterRequest, InterpreterSource,
    SourceSelector, VersionRequest,
};

use crate::virtualenv::{detect_virtualenv, virtualenv_python_executable};
use crate::PythonVersion;
use crate::{Error, Interpreter};

fn interpreter_sources_from_env() -> SourceSelector {
    if env::var_os("UV_FORCE_MANAGED_PYTHON").is_some() {
        debug!("Only considering managed toolchains due to `UV_FORCE_MANAGED_PYTHON`");
        SourceSelector::Some(HashSet::from_iter([InterpreterSource::ManagedToolchain]))
    } else if env::var_os("UV_TEST_PYTHON_PATH").is_some() {
        debug!("Only considering search path due to `UV_TEST_PYTHON_PATH`");
        SourceSelector::Some(HashSet::from_iter([InterpreterSource::SearchPath]))
    } else {
        SourceSelector::All
    }
}

/// Find a Python of a specific version, a binary with a name or a path to a binary.
///
/// Supported formats:
/// * `-p 3.10` searches for an installed Python 3.10 (`py --list-paths` on Windows, `python3.10` on
///   Linux/Mac). Specifying a patch version is not supported.
/// * `-p python3.10` or `-p python.exe` looks for a binary in `PATH`.
/// * `-p /home/ferris/.local/bin/python3.10` uses this exact Python.
///
/// When the user passes a patch version (e.g. 3.12.1), we currently search for a matching minor
/// version (e.g. `python3.12` on unix) and error when the version mismatches, as a binary with the
/// patch version (e.g. `python3.12.1`) is often not in `PATH` and we make the simplifying
/// assumption that the user has only this one patch version installed.
#[instrument(skip_all, fields(%request))]
pub fn find_requested_python(
    request: &str,
    cache: &Cache,
) -> Result<Option<Interpreter>, DiscoveryError> {
    debug!("Starting interpreter discovery for Python @ `{request}`");
    let request = InterpreterRequest::parse(request);
    let sources = interpreter_sources_from_env();
    Ok(find_interpreter(&request, &sources, cache)?
        .map(FindResult::into_interpreteter)
        .inspect(warn_on_unsupported_python))
}

/// Pick a sensible default for the Python a user wants when they didn't specify a version.
///
/// We prefer the test overwrite `UV_TEST_PYTHON_PATH` if it is set, otherwise `python3`/`python` or
/// `python.exe` respectively.
#[instrument(skip_all)]
pub fn find_default_python(cache: &Cache) -> Result<Interpreter, Error> {
    debug!("Starting interpreter discovery for default Python");
    try_find_default_python(cache)?.ok_or(if cfg!(windows) {
        Error::NoPythonInstalledWindows
    } else if cfg!(unix) {
        Error::NoPythonInstalledUnix
    } else {
        unreachable!("Only Unix and Windows are supported")
    })
}

/// Same as [`find_default_python`] but returns `None` if no python is found instead of returning an `Err`.
pub(crate) fn try_find_default_python(cache: &Cache) -> Result<Option<Interpreter>, Error> {
    let request = InterpreterRequest::Version(VersionRequest::Default);
    let sources = SourceSelector::Some(HashSet::from_iter([
        InterpreterSource::SearchPath,
        InterpreterSource::PyLauncher,
    ]));
    Ok(find_interpreter(&request, &sources, cache)?
        .map(FindResult::into_interpreteter)
        .inspect(warn_on_unsupported_python))
}

fn warn_on_unsupported_python(interpreter: &Interpreter) {
    // Warn on usage with an unsupported Python version
    if interpreter.python_tuple() < (3, 8) {
        warn_user_once!(
            "uv is only compatible with Python 3.8+, found Python {}.",
            interpreter.python_version()
        );
    }
}

/// Find a matching Python or any fallback Python.
///
/// If no Python version is provided, we will use the first available interpreter.
///
/// If a Python version is provided, we will first try to find an exact match. If
/// that cannot be found and a patch version was requested, we will look for a match
/// without comparing the patch version number. If that cannot be found, we fall back to
/// the first available version.
///
/// See [`Self::find_version`] for details on the precedence of Python lookup locations.
#[instrument(skip_all, fields(?python_version))]
pub fn find_best_python(
    python_version: Option<&PythonVersion>,
    system: bool,
    cache: &Cache,
) -> Result<Interpreter, Error> {
    if let Some(python_version) = python_version {
        debug!(
            "Starting interpreter discovery for Python {}",
            python_version
        );
    } else {
        debug!("Starting interpreter discovery for active Python");
    }

    // First, check for an exact match (or the first available version if no Python version was provided)
    if let Some(interpreter) = find_version(python_version, system, cache)? {
        warn_on_unsupported_python(&interpreter);
        return Ok(interpreter);
    }

    if let Some(python_version) = python_version {
        // If that fails, and a specific patch version was requested try again allowing a
        // different patch version
        if python_version.patch().is_some() {
            if let Some(interpreter) =
                find_version(Some(&python_version.without_patch()), system, cache)?
            {
                warn_on_unsupported_python(&interpreter);
                return Ok(interpreter);
            }
        }
    }

    // If a Python version was requested but cannot be fulfilled, just take any version
    if let Some(interpreter) = find_version(None, system, cache)? {
        return Ok(interpreter);
    }

    Err(Error::PythonNotFound)
}

/// Find a Python interpreter.
///
/// We check, in order, the following locations:
///
/// - `UV_DEFAULT_PYTHON`, which is set to the python interpreter when using `python -m uv`.
/// - `VIRTUAL_ENV` and `CONDA_PREFIX`
/// - A `.venv` folder
/// - If a python version is given: Search `PATH` and `py --list-paths`, see `find_python`
/// - `python3` (unix) or `python.exe` (windows)
///
/// If `UV_TEST_PYTHON_PATH` is set, we will not check for Python versions in the
/// global PATH, instead we will search using the provided path. Virtual environments
/// will still be respected.
///
/// If a version is provided and an interpreter cannot be found with the given version,
/// we will return [`None`].
fn find_version(
    python_version: Option<&PythonVersion>,
    system: bool,
    cache: &Cache,
) -> Result<Option<Interpreter>, Error> {
    let version_matches = |interpreter: &Interpreter| -> bool {
        if let Some(python_version) = python_version {
            // If a patch version was provided, check for an exact match
            interpreter.satisfies(python_version)
        } else {
            // The version always matches if one was not provided
            true
        }
    };

    // Check if the venv Python matches.
    if !system {
        if let Some(venv) = detect_virtualenv()? {
            let executable = virtualenv_python_executable(venv);
            let interpreter = Interpreter::query(executable, cache)?;

            if version_matches(&interpreter) {
                return Ok(Some(interpreter));
            }
        };
    }

    // Look for the requested version with by search for `python{major}.{minor}` in `PATH` on
    // Unix and `py --list-paths` on Windows.
    let interpreter = if let Some(python_version) = python_version {
        debug!("Starting interpreter discovery for Python @ `{python_version}`");
        let request = InterpreterRequest::Version(VersionRequest::from(python_version));
        let sources = SourceSelector::Some(HashSet::from_iter([
            InterpreterSource::SearchPath,
            InterpreterSource::PyLauncher,
        ]));
        find_interpreter(&request, &sources, cache)?
            .map(FindResult::into_interpreteter)
            .inspect(warn_on_unsupported_python)
    } else {
        try_find_default_python(cache)?
    };

    if let Some(interpreter) = interpreter {
        debug_assert!(version_matches(&interpreter));
        Ok(Some(interpreter))
    } else {
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use insta::assert_snapshot;
    use itertools::Itertools;

    use uv_cache::Cache;

    use crate::find_python::find_requested_python;
    use crate::Error;

    fn format_err<T: std::fmt::Debug>(err: Result<T, Error>) -> String {
        anyhow::Error::new(err.unwrap_err())
            .chain()
            .join("\n  Caused by: ")
    }

    #[test]
    #[cfg_attr(not(unix), ignore)]
    fn no_such_python_version() {
        let request = "3.1000";
        let result = find_requested_python(request, &Cache::temp().unwrap())
            .unwrap()
            .ok_or(Error::NoSuchPython(request.to_string()));
        assert_snapshot!(
            format_err(result),
            @"No Python 3.1000 in `PATH`. Is Python 3.1000 installed?"
        );
    }

    #[test]
    #[cfg_attr(not(unix), ignore)]
    fn no_such_python_binary() {
        let request = "python3.1000";
        let result = find_requested_python(request, &Cache::temp().unwrap())
            .unwrap()
            .ok_or(Error::NoSuchPython(request.to_string()));
        assert_snapshot!(
            format_err(result),
            @"No Python python3.1000 in `PATH`. Is Python python3.1000 installed?"
        );
    }

    #[test]
    #[cfg_attr(not(unix), ignore)]
    fn no_such_python_path() {
        let result = find_requested_python("/does/not/exists/python3.12", &Cache::temp().unwrap())
            .unwrap()
            .ok_or(Error::RequestedPythonNotFound(
                "/does/not/exists/python3.12".to_string(),
            ));
        assert_snapshot!(
            format_err(result), @"Failed to locate Python interpreter at `/does/not/exists/python3.12`");
    }
}
