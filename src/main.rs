use verus_docgenerator::tree_sitter_wrapper;
use verus_docgenerator::doc_item::*;
use verus_docgenerator::extraction;
use verus_docgenerator::markdown;

use std::path::{Path, PathBuf};

fn collect_rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(collect_rs_files(&path));
            } else if path.extension().map_or(false, |e| e == "rs") {
                files.push(path);
            }
        }
    }
    files
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    let mut input_dir = String::from(".");
    let mut output_file = String::from("docs.md");
    let mut src_prefix = String::from("./src/");

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--input" | "-i" => {
                i += 1;
                if i < args.len() {
                    input_dir = args[i].clone();
                }
            }
            "--output" | "-o" => {
                i += 1;
                if i < args.len() {
                    output_file = args[i].clone();
                }
            }
            "--src-prefix" => {
                i += 1;
                if i < args.len() {
                    src_prefix = args[i].clone();
                }
            }
            _ => {
                eprintln!("Unknown argument: {}", args[i]);
                std::process::exit(1);
            }
        }
        i += 1;
    }

    let input_path = Path::new(&input_dir);
    if !input_path.exists() {
        eprintln!("Input directory does not exist: {}", input_dir);
        std::process::exit(1);
    }

    let rs_files = collect_rs_files(input_path);
    eprintln!("Found {} .rs files in {}", rs_files.len(), input_dir);

    let mut all_items: Vec<RtDocItem> = Vec::new();

    for file_path in &rs_files {
        let source = match std::fs::read_to_string(file_path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("Warning: could not read {}: {}", file_path.display(), e);
                continue;
            }
        };

        let rel_path = file_path
            .strip_prefix(input_path)
            .unwrap_or(file_path)
            .to_string_lossy()
            .to_string();

        let module_path = rel_path
            .trim_end_matches(".rs")
            .replace('/', "::")
            .replace("mod::", "")
            .replace("::mod", "")
            .replace("lib", "crate");

        match tree_sitter_wrapper::extract_items(&source, &rel_path, &module_path) {
            Ok(items) => {
                all_items.extend(items);
            }
            Err(e) => {
                eprintln!("Warning: parse error in {}: {}", file_path.display(), e);
            }
        }
    }

    eprintln!("Extracted {} total items", all_items.len());

    // Filter to public items only
    let public_items: Vec<RtDocItem> = all_items
        .into_iter()
        .filter(|item| matches!(item.visibility, RtVisibility::Public))
        .collect();

    eprintln!("{} public items", public_items.len());

    // Group by module and sort
    let output = extraction::build_doc_output(public_items);

    // Generate markdown
    let md = markdown::format_doc_output(&output, &src_prefix);

    match std::fs::write(&output_file, &md) {
        Ok(()) => eprintln!("Wrote documentation to {}", output_file),
        Err(e) => {
            eprintln!("Error writing {}: {}", output_file, e);
            std::process::exit(1);
        }
    }
}
