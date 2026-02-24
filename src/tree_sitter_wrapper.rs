use crate::doc_item::*;

/// Extract documentation items from a Verus source file using tree-sitter.
pub fn extract_items(
    source: &str,
    file_path: &str,
    module_path: &str,
) -> Result<Vec<RtDocItem>, String> {
    let mut parser = tree_sitter::Parser::new();
    parser
        .set_language(&tree_sitter_verus::LANGUAGE.into())
        .map_err(|e| format!("Failed to load Verus grammar: {}", e))?;

    let tree = parser
        .parse(source.as_bytes(), None)
        .ok_or_else(|| "Failed to parse source".to_string())?;

    let root = tree.root_node();
    let mut items = Vec::new();

    collect_items_from_node(&root, source, file_path, module_path, &mut items);

    Ok(items)
}

/// Recursively collect documentation items from a tree-sitter node.
fn collect_items_from_node(
    node: &tree_sitter::Node,
    source: &str,
    file_path: &str,
    module_path: &str,
    items: &mut Vec<RtDocItem>,
) {
    let mut cursor = node.walk();

    for child in node.children(&mut cursor) {
        match child.kind() {
            "verus_block" => {
                // Recurse into verus_block to find function_items
                collect_items_from_node(&child, source, file_path, module_path, items);
            }
            "impl_item" => {
                // Recurse into impl blocks to find methods
                collect_items_from_impl(&child, source, file_path, module_path, items);
            }
            "function_item" | "function_signature_item" => {
                if let Some(item) = extract_function_item(&child, source, file_path, module_path) {
                    items.push(item);
                }
            }
            _ => {
                // Don't recurse into other node types (token_trees etc.)
            }
        }
    }
}

/// Collect function items from inside an impl block.
fn collect_items_from_impl(
    impl_node: &tree_sitter::Node,
    source: &str,
    file_path: &str,
    module_path: &str,
    items: &mut Vec<RtDocItem>,
) {
    // Get the type name for context
    let type_name = impl_node
        .child_by_field_name("type")
        .map(|n| node_text(&n, source))
        .unwrap_or_default();

    let impl_module = if type_name.is_empty() {
        module_path.to_string()
    } else {
        format!("{}::{}", module_path, type_name)
    };

    // Find the declaration_list (body)
    if let Some(body) = impl_node.child_by_field_name("body") {
        let mut cursor = body.walk();
        for child in body.children(&mut cursor) {
            match child.kind() {
                "function_item" | "function_signature_item" => {
                    if let Some(item) =
                        extract_function_item(&child, source, file_path, &impl_module)
                    {
                        items.push(item);
                    }
                }
                _ => {}
            }
        }
    }
}

/// Extract a single function item from a function_item or function_signature_item node.
fn extract_function_item(
    node: &tree_sitter::Node,
    source: &str,
    file_path: &str,
    module_path: &str,
) -> Option<RtDocItem> {
    let name = node.child_by_field_name("name")?;
    let name_text = node_text(&name, source);

    // Determine visibility
    let visibility = extract_visibility(node, source);

    // Determine function kind and open/closed from function_modifiers
    let (kind, is_open) = extract_fn_kind(node, source);

    // Get line number (1-based)
    let line_number = node.start_position().row + 1;

    // Extract doc comment from preceding sibling
    let doc_comment = extract_doc_comment(node, source);

    Some(RtDocItem {
        name: name_text,
        kind,
        visibility,
        is_open,
        line_number,
        file_path: file_path.to_string(),
        doc_comment,
        module_path: module_path.to_string(),
    })
}

/// Extract visibility from a node.
fn extract_visibility(node: &tree_sitter::Node, source: &str) -> RtVisibility {
    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "visibility_modifier" {
            let text = node_text(&child, source);
            if text.contains("crate") {
                return RtVisibility::PublicCrate;
            }
            return RtVisibility::Public;
        }
    }
    RtVisibility::Private
}

/// Extract function kind (spec/proof/exec) and open/closed status.
fn extract_fn_kind(node: &tree_sitter::Node, source: &str) -> (RtFnKind, bool) {
    let mut kind = RtFnKind::Exec;
    let mut is_open = false;

    let mut cursor = node.walk();
    for child in node.children(&mut cursor) {
        if child.kind() == "function_modifiers" {
            let mut mod_cursor = child.walk();
            for modifier in child.children(&mut mod_cursor) {
                match node_text(&modifier, source).as_str() {
                    "spec" => kind = RtFnKind::Spec,
                    "proof" => kind = RtFnKind::Proof,
                    "exec" => kind = RtFnKind::Exec,
                    "open" => is_open = true,
                    _ => {}
                }
            }
        }
    }

    (kind, is_open)
}

/// Extract doc comment text from preceding siblings (/// comments).
/// Handles both direct line_comment siblings and attribute_item nodes.
fn extract_doc_comment(node: &tree_sitter::Node, source: &str) -> Option<String> {
    let mut comments = Vec::new();
    let mut prev = node.prev_sibling();

    while let Some(sibling) = prev {
        if sibling.kind() == "line_comment" {
            let text = node_text(&sibling, source);
            if text.starts_with("///") {
                let doc_text = text.trim_start_matches("///").trim();
                comments.push(doc_text.to_string());
                prev = sibling.prev_sibling();
                continue;
            }
        } else if sibling.kind() == "attribute_item" {
            // Skip attributes like #[verifier::external] between doc comment and function
            prev = sibling.prev_sibling();
            continue;
        }
        break;
    }

    // If no doc comments found via siblings, try looking at the source text
    // directly above the function (handles cases where tree-sitter extras
    // aren't proper siblings)
    if comments.is_empty() {
        let start_byte = node.start_byte();
        let before = &source[..start_byte];
        let lines: Vec<&str> = before.lines().collect();

        // Walk backwards through preceding lines
        let mut i = lines.len();
        while i > 0 {
            i -= 1;
            let line = lines[i].trim();
            if line.starts_with("///") {
                let doc_text = line.trim_start_matches("///").trim();
                comments.push(doc_text.to_string());
            } else if line.is_empty() || line.starts_with("#[") {
                // Skip blank lines and attributes
                continue;
            } else {
                break;
            }
        }
    }

    if comments.is_empty() {
        None
    } else {
        comments.reverse();
        Some(comments.join(" "))
    }
}

/// Get the text content of a node.
fn node_text(node: &tree_sitter::Node, source: &str) -> String {
    node.utf8_text(source.as_bytes())
        .unwrap_or("")
        .to_string()
}
