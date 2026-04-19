use std::{env, path::PathBuf};

use bindgen::callbacks::{ItemKind, ParseCallbacks};
use convert_case::{Case, Casing as _};

#[cfg(feature = "static")]
use std::fs;
#[cfg(feature = "static")]
use std::path::Path;
use std::process::Command;

fn link_with(name: &str) {
    #[cfg(feature = "static")]
    println!("cargo:rustc-link-lib=static={name}");
    #[cfg(not(feature = "static"))]
    println!("cargo:rustc-link-lib=dylib={name}");
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=CVC5_LIB_DIR");
    println!("cargo:rerun-if-env-changed=DOCS_RS");

    // On docs.rs, skip building/linking cvc5 and use pre-generated bindings.
    if env::var("DOCS_RS").is_ok() {
        let out = PathBuf::from(env::var("OUT_DIR").unwrap());
        let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
        std::fs::copy(
            manifest.join("prebuilt/bindings.rs"),
            out.join("bindings.rs"),
        )
        .expect("Failed to copy pre-generated bindings");
        if cfg!(feature = "parser") {
            std::fs::copy(
                manifest.join("prebuilt/parser_bindings.rs"),
                out.join("parser_bindings.rs"),
            )
            .expect("Failed to copy pre-generated parser bindings");
        }
        return;
    }

    // If CVC5_LIB_DIR is set, resolve the path according to the given path
    let (include_dir, lib_dir) = if let Ok(lib_dir) = env::var("CVC5_LIB_DIR") {
        resolve_paths_given_lib_dir(PathBuf::from(lib_dir))
    } else {
        ensure_cvc5_built_and_install()
    };
    lib_dir.iter().for_each(|lib_dir| {
        println!("cargo:rustc-link-search=native={}", lib_dir.display());
    });

    link_with("cvc5");
    // Link parser library
    if cfg!(feature = "parser") {
        link_with("cvc5parser");
    }

    #[cfg(feature = "static")]
    for lib in &["cadical", "picpoly", "picpolyxx", "gmp", "cocoa"] {
        link_with(lib);
    }

    // Link C++ stdlib
    link_cxx_stdlib();

    // Generate bindings
    generate_bindings(include_dir);
}

/// Renames enums
#[derive(Debug)]
struct RenamingCallback;
impl ParseCallbacks for RenamingCallback {
    fn item_name(&self, item_info: bindgen::callbacks::ItemInfo<'_>) -> Option<String> {
        let prefix = match item_info.kind {
            ItemKind::Type => "Cvc5",
            ItemKind::Var => "CVC5_",
            ItemKind::Function => "cvc5_",
            _ => {
                return None;
            }
        };
        let name = item_info.name.strip_prefix(prefix)?;
        if name.is_empty() {
            // Special case for the solver
            return Some("Solver".to_string());
        };
        Some(name.to_string())
    }
    fn enum_variant_name(
        &self,
        enum_name: Option<&str>,
        variant: &str,
        _variant_value: bindgen::callbacks::EnumVariantValue,
    ) -> Option<String> {
        let enum_name = enum_name?;
        // For some reason, some enums start with `enum `
        let name = enum_name.strip_prefix("enum ").unwrap_or(enum_name);
        let prefix = match name {
            "Cvc5Kind" => "CVC5_KIND_",
            "Cvc5SortKind" => "CVC5_SORT_KIND_",
            "Cvc5RoundingMode" => "CVC5_RM_",
            "Cvc5UnknownExplanation" => "CVC5_UNKNOWN_EXPLANATION_",
            "Cvc5BlockModelsMode" => "CVC5_BLOCK_MODELS_MODE_",
            "Cvc5LearnedLitType" => "CVC5_LEARNED_LIT_TYPE_",
            "Cvc5ProofComponent" => "CVC5_PROOF_COMPONENT_",
            "Cvc5ProofFormat" => "CVC5_PROOF_FORMAT_",
            "Cvc5ProofRule" => "CVC5_PROOF_RULE_",
            "Cvc5ProofRewriteRule" => "CVC5_PROOF_REWRITE_RULE_",
            "Cvc5SkolemId" => "CVC5_SKOLEM_ID_",
            "Cvc5FindSynthTarget" => "CVC5_FIND_SYNTH_TARGET_",
            "Cvc5InputLanguage" => "CVC5_INPUT_LANGUAGE_",
            "Cvc5OptionCategory" => "CVC5_OPTION_CATEGORY_",
            "Cvc5OptionInfoKind" => "CVC5_OPTION_INFO_",
            _ => {
                return None;
            }
        };
        let result = variant
            .strip_prefix(prefix)
            .expect("Prefix")
            .from_case(Case::UpperSnake)
            .to_case(Case::Pascal);
        Some(result)
    }
}

fn generate_bindings(include_dir: Option<PathBuf>) {
    // Generate bindings from the C API header
    let header = "cvc5/c/cvc5.h";

    let builder = bindgen::Builder::default();
    let builder = match include_dir.as_ref() {
        Some(include_dir) => builder
            .header(include_dir.join(header).to_string_lossy())
            .clang_arg(format!("-I{}", include_dir.display())),
        None => builder.header(header),
    };

    let bindings = builder
        .parse_callbacks(Box::new(RenamingCallback))
        .clang_arg("-DCVC5_STATIC_DEFINE")
        .allowlist_function("cvc5_.*")
        .allowlist_type("Cvc5.*")
        .allowlist_var("CVC5_.*")
        .rustified_enum("Cvc5Kind")
        .rustified_enum("Cvc5SortKind")
        .rustified_enum("Cvc5RoundingMode")
        .rustified_enum("Cvc5UnknownExplanation")
        .rustified_enum("Cvc5BlockModelsMode")
        .rustified_enum("Cvc5LearnedLitType")
        .rustified_enum("Cvc5ProofComponent")
        .rustified_enum("Cvc5ProofFormat")
        .rustified_enum("Cvc5ProofRule")
        .rustified_enum("Cvc5ProofRewriteRule")
        .rustified_enum("Cvc5SkolemId")
        .rustified_enum("Cvc5FindSynthTarget")
        .rustified_enum("Cvc5InputLanguage")
        .rustified_enum("Cvc5OptionCategory")
        .rustified_enum("Cvc5OptionInfoKind")
        .generate_comments(true)
        .derive_default(true)
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate cvc5 bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    // Generate parser bindings if feature enabled
    if cfg!(feature = "parser") {
        let parser_header = "cvc5/c/cvc5_parser.h";
        let builder = bindgen::Builder::default();
        let builder = match include_dir.as_ref() {
            Some(include_dir) => builder
                .header(include_dir.join(parser_header).to_string_lossy())
                .clang_arg(format!("-I{}", include_dir.display())),
            None => builder.header(parser_header),
        };

        let parser_bindings = builder
            .clang_arg("-DCVC5_STATIC_DEFINE")
            .parse_callbacks(Box::new(RenamingCallback))
            .allowlist_function("cvc5_parser_.*")
            .allowlist_function("cvc5_cmd_.*")
            .allowlist_function("cvc5_symbol_manager_.*")
            .allowlist_function("cvc5_sm_.*")
            .allowlist_type("Cvc5InputParser")
            .allowlist_type("Cvc5SymbolManager")
            .allowlist_type("Cvc5Command")
            .allowlist_type("cvc5_cmd_t")
            .blocklist_type("Cvc5")
            .blocklist_type("Cvc5TermManager")
            .blocklist_type("Cvc5Sort")
            .blocklist_type("cvc5_sort_t")
            .blocklist_type("Cvc5Term")
            .blocklist_type("cvc5_term_t")
            .blocklist_type("Cvc5InputLanguage")
            .raw_line("use super::*;")
            .generate_comments(true)
            .derive_default(true)
            .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
            .generate()
            .expect("Unable to generate cvc5 parser bindings");

        parser_bindings
            .write_to_file(out_path.join("parser_bindings.rs"))
            .expect("Couldn't write parser bindings!");
    }
}

#[cfg(feature = "static")]
fn read_expected_cvc5_version() -> String {
    let manifest = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("Cargo.toml");
    let content = std::fs::read_to_string(&manifest).expect("Failed to read Cargo.toml");
    let table: toml::Table = content.parse().expect("Failed to parse Cargo.toml");
    table["package"]["metadata"]["cvc5"]["version"]
        .as_str()
        .expect("Missing version in [package.metadata.cvc5]")
        .to_string()
}

#[cfg(feature = "static")]
fn check_cvc5_version(cvc5_dir: &Path, expected: &str) {
    let version_file = cvc5_dir.join("cmake/version-base.cmake");
    assert!(
        version_file.exists(),
        "cvc5 version file not found at {}",
        version_file.display()
    );

    let content = std::fs::read_to_string(&version_file)
        .unwrap_or_else(|e| panic!("Failed to read {}: {e}", version_file.display()));

    let version = content
        .lines()
        .find_map(|line| {
            line.strip_prefix("set(CVC5_LAST_RELEASE \"")
                .and_then(|rest| rest.strip_suffix("\")"))
        })
        .unwrap_or_else(|| panic!("CVC5_LAST_RELEASE not found in {}", version_file.display()));

    assert_eq!(
        version, expected,
        "cvc5 version mismatch: found {version}, expected {expected}. \
         Update the cvc5 submodule or change version in [package.metadata.cvc5] in Cargo.toml."
    );

    println!("cargo:rerun-if-changed={}", version_file.display());
}

// return (include path, lib path) if exist

#[cfg(unix)]
#[cfg(feature = "static")]
fn ensure_cvc5_built_and_install() -> (Option<PathBuf>, Option<PathBuf>) {
    let cvc5_dir = find_cvc5_dir();
    let expected = read_expected_cvc5_version();
    check_cvc5_version(&cvc5_dir, &expected);
    let include_dir =
        find_cvc5_include_dir().unwrap_or_else(|| cvc5_dir.join("build/install/include"));
    if cvc5_dir.join("build/install/lib/libcvc5.a").exists() {
        return (Some(include_dir), Some(cvc5_dir.join("build/install/lib")));
    }
    if cvc5_dir.join("build/install/lib64/libcvc5.a").exists() {
        return (
            Some(include_dir),
            Some(cvc5_dir.join("build/install/lib64")),
        );
    }

    eprintln!("cvc5 not yet built — running configure and make (this may take a while)...");

    let configure = cvc5_dir.join("configure.sh");
    assert!(
        configure.exists(),
        "configure.sh not found at {}",
        configure.display()
    );

    let build_dir = cvc5_dir.join("build");

    let status = Command::new("bash")
        .arg(&configure)
        .arg("--static")
        .arg("--auto-download")
        .arg("--cocoa")
        .arg("--gpl")
        .arg(format!("--prefix={}/install", build_dir.display()))
        .arg("-DBUILD_GMP=1")
        .current_dir(&cvc5_dir)
        .status()
        .expect("Failed to run configure.sh");
    assert!(status.success(), "cvc5 configure.sh failed");

    let jobs = std::thread::available_parallelism()
        .map(|n| n.get().to_string())
        .unwrap_or_else(|_| "4".to_string());

    let status = Command::new("make")
        .arg(format!("-j{jobs}"))
        .current_dir(cvc5_dir.join("build"))
        .status()
        .expect("Failed to run make");
    assert!(status.success(), "cvc5 build failed");

    let status = Command::new("make")
        .arg("install")
        .current_dir(cvc5_dir.join("build"))
        .status()
        .expect("Failed to run make");
    assert!(status.success(), "cvc5 install failed");
    let lib_dir = {
        let p = cvc5_dir.join("build/install/lib");
        if p.exists() {
            p
        } else {
            let p = cvc5_dir.join("build/install/lib64");
            if p.exists() {
                p
            } else {
                panic!("Not able to find a lib folder in {}!", build_dir.display());
            }
        }
    };

    // GMP work around; c.f. https://github.com/cvc5/cvc5/pull/12168
    for file in glob::glob(&build_dir.join("deps/lib/libgmp.*").to_string_lossy()).unwrap() {
        let file = file.unwrap();
        let dest = lib_dir.join(file.file_name().unwrap());
        fs::copy(file, dest).unwrap();
    }

    (Some(include_dir), Some(lib_dir))
}

#[cfg(not(unix))]
#[cfg(feature = "static")]
fn ensure_cvc5_built_and_install() -> (Option<PathBuf>, Option<PathBuf>) {
    panic!("This rust binding for cvc5 is only supported on Unix systems!.");
}

/// Ask the C compiler to resolve `cvc5/c/cvc5.h` and return its include
/// directory (the parent of `cvc5/`).
fn discover_include_dir() -> Option<PathBuf> {
    let compiler = cc::Build::new().cargo_warnings(false).get_compiler();
    let output = Command::new(compiler.path())
        .args(compiler.args())
        .args(["-E", "-M", "-xc", "-"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null())
        .spawn()
        .and_then(|mut child| {
            use std::io::Write;
            child
                .stdin
                .take()
                .unwrap()
                .write_all(b"#include <cvc5/c/cvc5.h>\n")?;
            child.wait_with_output()
        })
        .ok()?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let suffix = "/cvc5/c/cvc5.h";
    stdout.split_whitespace().find_map(|token| {
        let path = token.strip_suffix(suffix)?;
        Some(PathBuf::from(path))
    })
}

#[cfg(not(feature = "static"))]
fn ensure_cvc5_built_and_install() -> (Option<PathBuf>, Option<PathBuf>) {
    (find_cvc5_include_dir().or_else(discover_include_dir), None)
}

fn find_cvc5_include_dir() -> Option<PathBuf> {
    println!("cargo:rerun-if-env-changed=CVC5_INCLUDE_DIR");
    match env::var("CVC5_INCLUDE_DIR") {
        Ok(d) => Some(PathBuf::from(d)),
        Err(_) => None,
    }
}

#[cfg(feature = "static")]
fn find_cvc5_dir() -> PathBuf {
    // 1. Check CVC5_DIR env var
    println!("cargo:rerun-if-env-changed=CVC5_DIR");
    if let Ok(dir) = env::var("CVC5_DIR") {
        let p = PathBuf::from(dir);
        if p.exists() {
            return p;
        }
    }

    // 2. Check for cvc5 directory inside cvc5-sys (submodule)
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let local = manifest_dir.join("cvc5");
    if local.join("include/cvc5/c/cvc5.h").exists() {
        return local;
    }

    // 3. Clone into OUT_DIR (safe during cargo publish)
    let out = PathBuf::from(env::var("OUT_DIR").unwrap()).join("cvc5");
    if out.join("include/cvc5/c/cvc5.h").exists() {
        return out;
    }

    let expected = read_expected_cvc5_version();
    let tag = format!("cvc5-{expected}");
    eprintln!("cvc5 source not found — cloning tag {tag} from GitHub...");

    let status = Command::new("git")
        .args(["clone", "--depth", "1", "--branch", &tag])
        .arg("https://github.com/cvc5/cvc5.git")
        .arg(&out)
        .status()
        .expect("Failed to run git clone — is git installed?");
    assert!(status.success(), "git clone of cvc5 tag {tag} failed");

    out
}

fn resolve_paths_given_lib_dir(lib_dir: PathBuf) -> (Option<PathBuf>, Option<PathBuf>) {
    assert!(
        lib_dir.exists(),
        "CVC5_LIB_DIR does not exist: {}",
        lib_dir.display()
    );

    // Find include directory
    let include_dir = find_cvc5_include_dir().unwrap_or_else(|| lib_dir.join("../include"));
    let include_dir = include_dir
        .canonicalize()
        .ok()
        .or_else(discover_include_dir)
        .unwrap_or_else(|| {
            panic!(
                "Include directory not found. Set CVC5_INCLUDE_DIR or ensure \
             {}/include exists.",
                lib_dir.join("..").display()
            )
        });

    (Some(include_dir), Some(lib_dir))
}

fn link_cxx_stdlib() {
    let cxx = match env::var("CXXSTDLIB") {
        Ok(s) if s.is_empty() => None,
        Ok(s) => Some(s),
        Err(_) => {
            let target = env::var("TARGET").unwrap();
            if target.contains("msvc") {
                None
            } else if target.contains("apple") || target.contains("freebsd") {
                Some("c++".to_string())
            } else {
                Some("stdc++".to_string())
            }
        }
    };
    if let Some(cxx) = cxx {
        println!("cargo:rustc-link-lib={cxx}");
    }

    // On RHEL/CentOS with GCC toolsets (e.g. gcc-toolset-10), newer C++ symbols
    // live in libstdc++_nonshared.a rather than the base system libstdc++.so.
    // If cvc5 was compiled with such a GCC, we must link this supplemental library.
    #[cfg(feature = "static")]
    if let Ok(output) = Command::new(cc::Build::new().cpp(true).get_compiler().path())
        .arg("-print-search-dirs")
        .output()
    {
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            if let Some(dirs) = line.strip_prefix("libraries: =") {
                for dir in dirs.split(':') {
                    let dir = Path::new(dir);
                    if dir.join("libstdc++_nonshared.a").exists() {
                        println!("cargo:rustc-link-search=native={}", dir.display());
                        println!("cargo:rustc-link-lib=static=stdc++_nonshared");
                        return;
                    }
                }
            }
        }
    }
}
