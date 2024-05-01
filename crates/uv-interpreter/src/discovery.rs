use itertools::Itertools;
use thiserror::Error;
use uv_cache::Cache;
use uv_fs::Simplified;
use which::which;

use crate::implementation::ImplementationName;
use crate::managed::toolchains_for_current_platform;
use crate::py_launcher::py_list_paths;
use crate::virtualenv::virtualenv_python_executable;
use crate::virtualenv::{virtualenv_from_env, virtualenv_from_working_dir};
use crate::{Interpreter, PythonVersion};
use std::borrow::Cow;

use std::collections::HashSet;
use std::fmt::{self, Formatter};
use std::num::ParseIntError;
use std::{env, io};
use std::{path::Path, path::PathBuf, str::FromStr};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct InterpreterFinder {
    request: InterpreterRequest,
    sources: SourceSelector,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterpreterRequest {
    /// A Python version without an implementation name
    Version(VersionRequest),
    /// A path to a directory containing a Python installation
    Directory(PathBuf),
    /// A path to a Python executable
    File(PathBuf),
    /// The name of a Python executable (i.e. for lookup in the PATH)
    ExecutableName(String),
    /// A Python implementation without a version
    Implementation(ImplementationName),
    /// A Python implementation name and version
    ImplementationVersion(ImplementationName, VersionRequest),
}

impl fmt::Display for InterpreterRequest {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Version(version) => write!(f, "python@{version}"),
            Self::Directory(path) => write!(f, "directory {}", path.user_display()),
            Self::File(path) => write!(f, "file {}", path.user_display()),
            Self::ExecutableName(name) => write!(f, "executable `{name}`"),
            Self::Implementation(implementation) => {
                write!(f, "{implementation}")
            }
            Self::ImplementationVersion(implementation, version) => {
                write!(f, "{implementation}@{version}")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum SourceSelector {
    #[default]
    All,
    Some(HashSet<InterpreterSource>),
}

impl SourceSelector {
    fn contains(&self, source: InterpreterSource) -> bool {
        match self {
            Self::All => true,
            Self::Some(sources) => sources.contains(&source),
        }
    }
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub enum VersionRequest {
    #[default]
    Default,
    Major(u8),
    MajorMinor(u8, u8),
    MajorMinorPatch(u8, u8, u8),
}

impl From<&PythonVersion> for VersionRequest {
    fn from(version: &PythonVersion) -> Self {
        Self::from_str(&version.string)
            .expect("Valid `PythonVersion`s should be valid `VersionRequest`s")
    }
}

impl fmt::Display for VersionRequest {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Default => f.write_str("default"),
            Self::Major(major) => write!(f, "{major}"),
            Self::MajorMinor(major, minor) => write!(f, "{major}.{minor}"),
            Self::MajorMinorPatch(major, minor, patch) => {
                write!(f, "{major}.{minor}.{patch}")
            }
        }
    }
}

impl fmt::Display for InterpreterSource {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::ProvidedPath => f.write_str("provided path"),
            Self::ActiveEnvironment => f.write_str("active environment"),
            Self::DiscoveredEnvironment => f.write_str("discovered environment"),
            Self::SearchPath => f.write_str("search path"),
            Self::PyLauncher => f.write_str("`py` launcher"),
            Self::ManagedToolchain => f.write_str("managed toolchain"),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct FindResult {
    source: InterpreterSource,
    interpreter: Interpreter,
}

#[derive(Debug, Clone, PartialEq, Eq, Copy, Hash)]
pub enum InterpreterSource {
    /// The interpreter path was provided directly
    ProvidedPath,
    /// An environment was active e.g. via `VIRTUAL_ENV`
    ActiveEnvironment,
    /// An environment was discovered e.g. via `.venv`
    DiscoveredEnvironment,
    /// An executable was found in the search path i.e. `PATH`
    SearchPath,
    /// An executable was found via the `py` launcher
    PyLauncher,
    /// The interpreter was found in the uv toolchain directory
    ManagedToolchain,
    // TODO(zanieb): Add support for fetching the interpreter from a remote source
    // TODO(zanieb): Add variant for: The interpreter path was inherited from the parent process
}

#[derive(Error, Debug)]
pub enum Error {
    #[error(transparent)]
    IO(#[from] io::Error),
    #[error(transparent)]
    Query(#[from] crate::interpreter::Error),
    #[error(transparent)]
    ManagedToolchain(#[from] crate::managed::Error),
    #[error(transparent)]
    VirtualEnv(#[from] crate::virtualenv::Error),
    #[error(transparent)]
    PyLauncher(#[from] crate::py_launcher::Error),
    #[error("Interpreter discovery for `{0}` requires `{1}` but it is not selected")]
    SourceNotSelected(InterpreterRequest, InterpreterSource),
}

/// Lazily iterate over all discoverable Python executables.
///
/// A [`VersionRequest`] may be provided, adjusting the possible executables.
/// The [`SourceSelector`] is used to filter the sources of the executables, sources that
/// are not selected will not be queried.
fn python_executables<'a>(
    version: Option<&'a VersionRequest>,
    sources: &'a SourceSelector,
) -> impl Iterator<Item = Result<(InterpreterSource, PathBuf), Error>> + 'a {
    // Note we are careful to ensure the iterator chain is lazy to avoid unnecessary work
    let iter =
        // (1) The active environment
        sources.contains(InterpreterSource::ActiveEnvironment).then(||
            virtualenv_from_env()
            .into_iter()
            .map(virtualenv_python_executable)
            .map(|path| Ok((InterpreterSource::ActiveEnvironment, path)))
        ).into_iter().flatten()
        // (2) A discovered environment
        .chain(
            sources.contains(InterpreterSource::DiscoveredEnvironment).then(||
                std::iter::once(
                    virtualenv_from_working_dir()
                    .map(|path|
                        path
                        .map(virtualenv_python_executable)
                        .map(|path| (InterpreterSource::DiscoveredEnvironment, path))
                        .into_iter()
                    )
                    .map_err(Error::from)
                ).flatten_ok()
            ).into_iter().flatten()
        )
        // (3) Managed toolchains
        .chain(
            sources.contains(InterpreterSource::ManagedToolchain).then(move ||
                std::iter::once(
                    toolchains_for_current_platform()
                    .map(|toolchains|
                        // Check that the toolchain version satisfies the request to avoid unnecessary interpreter queries later
                        toolchains.filter(move |toolchain|
                            version.is_none()
                            || version.is_some_and(|version| version.matches_version(&toolchain.python_version()))
                        )
                        .map(|toolchain| (InterpreterSource::ManagedToolchain, toolchain.executable()))
                    )
                    .map_err(Error::from)
                ).flatten_ok()
            ).into_iter().flatten()

        )
        // (4) The search path
        .chain(
            sources.contains(InterpreterSource::SearchPath).then(move ||
                python_executables_from_search_path(version)
                .map(|path| Ok((InterpreterSource::SearchPath, path))),
            ).into_iter().flatten()
        )
        // (5) The `py` launcher (windows only)
        // TODO(konstin): Implement <https://peps.python.org/pep-0514/> to read python installations from the registry instead.
        .chain(
            (sources.contains(InterpreterSource::PyLauncher) && cfg!(windows)).then(||
                std::iter::once(
                    py_list_paths()
                    .map(|entries|
                        // We can avoid querying the interpreter using versions from the py launcher output unless a patch is requested
                        entries.into_iter().filter(move |entry|
                            version.is_none()
                            || version.is_some_and(
                                |version| version.has_patch() || version.matches_major_minor(entry.major, entry.minor)
                            )
                        )
                        .map(|entry| (InterpreterSource::PyLauncher, entry.executable_path))
                    )
                    .map_err(Error::from)
                ).flatten_ok()
            ).into_iter().flatten()
        );

    iter
}

fn python_executables_from_search_path(
    version: Option<&VersionRequest>,
) -> impl Iterator<Item = PathBuf> + '_ {
    let search_path =
        env::var_os("UV_TEST_PYTHON_PATH").unwrap_or(env::var_os("PATH").unwrap_or_default());
    let search_dirs: Vec<_> = env::split_paths(&search_path).collect();
    let possible_names = version.unwrap_or(&VersionRequest::Default).possible_names();

    search_dirs.into_iter().flat_map(move |dir| {
        // Clone the directory for second closure
        let dir_clone = dir.clone();
        possible_names
            .clone()
            .into_iter()
            .flatten()
            .flat_map(move |name| {
                which::which_in_global(&*name, Some(&dir))
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>()
            })
            .filter(|path| !is_windows_store_shim(path))
            .chain(
                // TODO(zanieb): Consider moving `python.bat` into `possible_names` to avoid a chain
                cfg!(windows)
                    .then(move || {
                        which::which_in_global("python.bat", Some(&dir_clone))
                            .into_iter()
                            .flatten()
                            .collect::<Vec<_>>()
                    })
                    .into_iter()
                    .flatten(),
            )
    })
}

// Lazily iterate over all discoverable Python interpreters.
///
/// A [`VersionRequest`] may be provided, expanding the executable name search.
fn python_interpreters<'a>(
    version: Option<&'a VersionRequest>,
    sources: &'a SourceSelector,
    cache: &'a Cache,
) -> impl Iterator<Item = Result<(InterpreterSource, Interpreter), Error>> + 'a {
    let iter = python_executables(version, sources).map(|result| match result {
        Ok((source, path)) => Interpreter::query(path, cache)
            .map(|interpreter| (source, interpreter))
            .map_err(Error::from),
        Err(err) => Err(err),
    });

    iter
}

pub(crate) fn find_interpreter(
    request: &InterpreterRequest,
    sources: &SourceSelector,
    cache: &Cache,
) -> Result<Option<FindResult>, Error> {
    let result = match request {
        InterpreterRequest::File(path) => {
            if !sources.contains(InterpreterSource::ProvidedPath) {
                return Err(Error::SourceNotSelected(
                    request.clone(),
                    InterpreterSource::ProvidedPath,
                ));
            }
            if !path.try_exists()? {
                return Ok(None);
            }
            FindResult {
                source: InterpreterSource::ProvidedPath,
                interpreter: Interpreter::query(path, cache)?,
            }
        }
        InterpreterRequest::Directory(path) => {
            if !sources.contains(InterpreterSource::ProvidedPath) {
                return Err(Error::SourceNotSelected(
                    request.clone(),
                    InterpreterSource::ProvidedPath,
                ));
            }
            if !path.try_exists()? {
                return Ok(None);
            }
            let executable = virtualenv_python_executable(path);
            if !executable.try_exists()? {
                return Ok(None);
            }
            FindResult {
                source: InterpreterSource::ProvidedPath,
                interpreter: Interpreter::query(executable, cache)?,
            }
        }
        InterpreterRequest::ExecutableName(name) => {
            if !sources.contains(InterpreterSource::SearchPath) {
                return Err(Error::SourceNotSelected(
                    request.clone(),
                    InterpreterSource::SearchPath,
                ));
            }
            let Some(executable) = which(name).ok() else {
                return Ok(None);
            };
            FindResult {
                source: InterpreterSource::SearchPath,
                interpreter: Interpreter::query(executable, cache)?,
            }
        }
        InterpreterRequest::Implementation(implementation) => {
            let Some((source, interpreter)) = python_interpreters(None, sources, cache)
                .find(|result| {
                    result.is_err()
                        || result.as_ref().is_ok_and(|(_source, interpreter)| {
                            interpreter.implementation_name() == implementation.as_str()
                        })
                })
                .transpose()?
            else {
                return Ok(None);
            };
            FindResult {
                source,
                interpreter,
            }
        }
        InterpreterRequest::ImplementationVersion(implementation, version) => {
            let Some((source, interpreter)) = python_interpreters(Some(version), sources, cache)
                .find(|result| {
                    result.is_err()
                        || result.as_ref().is_ok_and(|(_source, interpreter)| {
                            version.matches_interpreter(interpreter)
                                && interpreter.implementation_name() == implementation.as_str()
                        })
                })
                .transpose()?
            else {
                return Ok(None);
            };
            FindResult {
                source,
                interpreter,
            }
        }
        InterpreterRequest::Version(version) => {
            let Some((source, interpreter)) = python_interpreters(Some(version), sources, cache)
                .find(|result| {
                    result.is_err()
                        || result.as_ref().is_ok_and(|(_source, interpreter)| {
                            version.matches_interpreter(interpreter)
                        })
                })
                .transpose()?
            else {
                return Ok(None);
            };
            FindResult {
                source,
                interpreter,
            }
        }
    };

    Ok(Some(result))
}

impl InterpreterRequest {
    /// Create a request from a string.
    ///
    /// This cannot fail, which means weird inputs will be parsed as [`InterpreterRequest::File`] or [`InterpreterRequest::ExecutableName`].
    pub(crate) fn parse(value: &str) -> Self {
        // e.g. `3.12.1`
        if let Ok(version) = VersionRequest::from_str(value) {
            return Self::Version(version);
        }
        // e.g. `python3.12.1`
        if let Some(remainder) = value.strip_prefix("python") {
            if let Ok(version) = VersionRequest::from_str(remainder) {
                return Self::Version(version);
            }
        }
        // e.g. `pypy@3.12`
        if let Some((first, second)) = value.split_once('@') {
            if let Ok(implementation) = ImplementationName::from_str(first) {
                if let Ok(version) = VersionRequest::from_str(second) {
                    return Self::ImplementationVersion(implementation, version);
                }
            }
        }
        for implementation in ImplementationName::iter() {
            if let Some(remainder) = value
                .to_ascii_lowercase()
                .strip_prefix(implementation.as_str())
            {
                // e.g. `pypy`
                if remainder.is_empty() {
                    return Self::Implementation(*implementation);
                }
                // e.g. `pypy3.12`
                if let Ok(version) = VersionRequest::from_str(remainder) {
                    return Self::ImplementationVersion(*implementation, version);
                }
            }
        }
        let value_as_path = PathBuf::from(value);
        // e.g. ./path/to/.venv
        if value_as_path.is_dir() {
            return Self::Directory(value_as_path);
        }
        // e.g. ./path/to/python3.exe
        // If it contains a path separator, we'll treat it as a full path even if it does not exist
        if value.contains(std::path::MAIN_SEPARATOR) {
            return Self::File(value_as_path);
        }
        // Finally, we'll treat it as the name of an executable (i.e. in the search PATH)
        // e.g. foo.exe
        Self::ExecutableName(value.to_string())
    }
}

impl VersionRequest {
    pub(crate) fn possible_names(self) -> [Option<Cow<'static, str>>; 4] {
        let (python, python3, extension) = if cfg!(windows) {
            (
                Cow::Borrowed("python.exe"),
                Cow::Borrowed("python3.exe"),
                ".exe",
            )
        } else {
            (Cow::Borrowed("python"), Cow::Borrowed("python3"), "")
        };

        match self {
            Self::Default => [Some(python3), Some(python), None, None],
            Self::Major(major) => [
                Some(Cow::Owned(format!("python{major}{extension}"))),
                Some(python),
                None,
                None,
            ],
            Self::MajorMinor(major, minor) => [
                Some(Cow::Owned(format!("python{major}.{minor}{extension}"))),
                Some(Cow::Owned(format!("python{major}{extension}"))),
                Some(python),
                None,
            ],
            Self::MajorMinorPatch(major, minor, patch) => [
                Some(Cow::Owned(format!(
                    "python{major}.{minor}.{patch}{extension}",
                ))),
                Some(Cow::Owned(format!("python{major}.{minor}{extension}"))),
                Some(Cow::Owned(format!("python{major}{extension}"))),
                Some(python),
            ],
        }
    }

    /// Check if a interpreter matches the requested Python version.
    fn matches_interpreter(self, interpreter: &Interpreter) -> bool {
        match self {
            Self::Default => true,
            Self::Major(major) => interpreter.python_major() == major,
            Self::MajorMinor(major, minor) => {
                (interpreter.python_major(), interpreter.python_minor()) == (major, minor)
            }
            Self::MajorMinorPatch(major, minor, patch) => {
                (
                    interpreter.python_major(),
                    interpreter.python_minor(),
                    interpreter.python_patch(),
                ) == (major, minor, patch)
            }
        }
    }

    fn matches_version(self, version: &PythonVersion) -> bool {
        match self {
            Self::Default => true,
            Self::Major(major) => version.major() == major,
            Self::MajorMinor(major, minor) => (version.major(), version.minor()) == (major, minor),
            Self::MajorMinorPatch(major, minor, patch) => {
                (version.major(), version.minor(), version.patch()) == (major, minor, Some(patch))
            }
        }
    }

    fn matches_major_minor(self, major: u8, minor: u8) -> bool {
        match self {
            Self::Default => true,
            Self::Major(self_major) => self_major == major,
            Self::MajorMinor(self_major, self_minor) => (self_major, self_minor) == (major, minor),
            Self::MajorMinorPatch(self_major, self_minor, _) => {
                (self_major, self_minor) == (major, minor)
            }
        }
    }

    fn has_patch(self) -> bool {
        match self {
            Self::Default => false,
            Self::Major(..) => false,
            Self::MajorMinor(..) => false,
            Self::MajorMinorPatch(..) => true,
        }
    }
}

impl FromStr for VersionRequest {
    type Err = ParseIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let versions = s
            .splitn(3, '.')
            .map(str::parse::<u8>)
            .collect::<Result<Vec<_>, _>>()?;

        let selector = match versions.as_slice() {
            // e.g. `3`
            [major] => VersionRequest::Major(*major),
            // e.g. `3.10`
            [major, minor] => VersionRequest::MajorMinor(*major, *minor),
            // e.g. `3.10.4`
            [major, minor, patch] => VersionRequest::MajorMinorPatch(*major, *minor, *patch),
            _ => unreachable!(),
        };

        Ok(selector)
    }
}

/// On Windows we might encounter the Windows Store proxy shim (enabled in:
/// Settings/Apps/Advanced app settings/App execution aliases). When Python is _not_ installed
/// via the Windows Store, but the proxy shim is enabled, then executing `python.exe` or
/// `python3.exe` will redirect to the Windows Store installer.
///
/// We need to detect that these `python.exe` and `python3.exe` files are _not_ Python
/// executables.
///
/// This method is taken from Rye:
///
/// > This is a pretty dumb way.  We know how to parse this reparse point, but Microsoft
/// > does not want us to do this as the format is unstable.  So this is a best effort way.
/// > we just hope that the reparse point has the python redirector in it, when it's not
/// > pointing to a valid Python.
///
/// See: <https://github.com/astral-sh/rye/blob/b0e9eccf05fe4ff0ae7b0250a248c54f2d780b4d/rye/src/cli/shim.rs#L108>
#[cfg(windows)]
pub(crate) fn is_windows_store_shim(path: &Path) -> bool {
    use std::os::windows::fs::MetadataExt;
    use std::os::windows::prelude::OsStrExt;
    use winapi::um::fileapi::{CreateFileW, OPEN_EXISTING};
    use winapi::um::handleapi::{CloseHandle, INVALID_HANDLE_VALUE};
    use winapi::um::ioapiset::DeviceIoControl;
    use winapi::um::winbase::{FILE_FLAG_BACKUP_SEMANTICS, FILE_FLAG_OPEN_REPARSE_POINT};
    use winapi::um::winioctl::FSCTL_GET_REPARSE_POINT;
    use winapi::um::winnt::{FILE_ATTRIBUTE_REPARSE_POINT, MAXIMUM_REPARSE_DATA_BUFFER_SIZE};

    // The path must be absolute.
    if !path.is_absolute() {
        return false;
    }

    // The path must point to something like:
    //   `C:\Users\crmar\AppData\Local\Microsoft\WindowsApps\python3.exe`
    let mut components = path.components().rev();

    // Ex) `python.exe` or `python3.exe`
    if !components
        .next()
        .and_then(|component| component.as_os_str().to_str())
        .is_some_and(|component| component == "python.exe" || component == "python3.exe")
    {
        return false;
    }

    // Ex) `WindowsApps`
    if !components
        .next()
        .is_some_and(|component| component.as_os_str() == "WindowsApps")
    {
        return false;
    }

    // Ex) `Microsoft`
    if !components
        .next()
        .is_some_and(|component| component.as_os_str() == "Microsoft")
    {
        return false;
    }

    // The file is only relevant if it's a reparse point.
    let Ok(md) = fs_err::symlink_metadata(path) else {
        return false;
    };
    if md.file_attributes() & FILE_ATTRIBUTE_REPARSE_POINT == 0 {
        return false;
    }

    let mut path_encoded = path
        .as_os_str()
        .encode_wide()
        .chain(std::iter::once(0))
        .collect::<Vec<_>>();

    // SAFETY: The path is null-terminated.
    #[allow(unsafe_code)]
    let reparse_handle = unsafe {
        CreateFileW(
            path_encoded.as_mut_ptr(),
            0,
            0,
            std::ptr::null_mut(),
            OPEN_EXISTING,
            FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT,
            std::ptr::null_mut(),
        )
    };

    if reparse_handle == INVALID_HANDLE_VALUE {
        return false;
    }

    let mut buf = [0u16; MAXIMUM_REPARSE_DATA_BUFFER_SIZE as usize];
    let mut bytes_returned = 0;

    // SAFETY: The buffer is large enough to hold the reparse point.
    #[allow(unsafe_code, clippy::cast_possible_truncation)]
    let success = unsafe {
        DeviceIoControl(
            reparse_handle,
            FSCTL_GET_REPARSE_POINT,
            std::ptr::null_mut(),
            0,
            buf.as_mut_ptr().cast(),
            buf.len() as u32 * 2,
            &mut bytes_returned,
            std::ptr::null_mut(),
        ) != 0
    };

    // SAFETY: The handle is valid.
    #[allow(unsafe_code)]
    unsafe {
        CloseHandle(reparse_handle);
    }

    // If the operation failed, assume it's not a reparse point.
    if !success {
        return false;
    }

    let reparse_point = String::from_utf16_lossy(&buf[..bytes_returned as usize]);
    reparse_point.contains("\\AppInstallerPythonRedirector.exe")
}

/// On Unix, we do not need to deal with Windows store shims.
///
/// See the Windows implementation for details.
#[cfg(not(windows))]
fn is_windows_store_shim(_path: &Path) -> bool {
    false
}

impl FindResult {
    #[allow(dead_code)]
    pub(crate) fn source(&self) -> &InterpreterSource {
        &self.source
    }

    #[allow(dead_code)]
    pub(crate) fn interpreteter(&self) -> &Interpreter {
        &self.interpreter
    }

    pub(crate) fn into_interpreteter(self) -> Interpreter {
        self.interpreter
    }
}
#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::{
        discovery::{InterpreterRequest, VersionRequest},
        implementation::ImplementationName,
    };

    #[test]
    fn python_request_from_str() {
        assert_eq!(
            InterpreterRequest::parse("3.12"),
            InterpreterRequest::Version(VersionRequest::from_str("3.12").unwrap())
        );
        assert_eq!(
            InterpreterRequest::parse("foo"),
            InterpreterRequest::ExecutableName("foo".to_string())
        );
        assert_eq!(
            InterpreterRequest::parse("cpython"),
            InterpreterRequest::Implementation(ImplementationName::Cpython)
        );
        assert_eq!(
            InterpreterRequest::parse("cpython3.12.2"),
            InterpreterRequest::ImplementationVersion(
                ImplementationName::Cpython,
                VersionRequest::from_str("3.12.2").unwrap()
            )
        );
    }

    #[test]
    fn python_version_request_from_str() {
        assert_eq!(VersionRequest::from_str("3"), Ok(VersionRequest::Major(3)));
        assert_eq!(
            VersionRequest::from_str("3.12"),
            Ok(VersionRequest::MajorMinor(3, 12))
        );
        assert_eq!(
            VersionRequest::from_str("3.12.1"),
            Ok(VersionRequest::MajorMinorPatch(3, 12, 1))
        );
        assert!(VersionRequest::from_str("1.foo.1").is_err());
    }
}
