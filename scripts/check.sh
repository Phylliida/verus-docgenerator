#!/bin/bash
set -e

echo "=== Building verus-docgenerator ==="
cargo build -p verus-docgenerator

echo ""
echo "=== Running verus-docgenerator on verus-rational ==="
cargo run -p verus-docgenerator -- --input ../verus-rational/src --output /tmp/verus-rational-docs.md

echo ""
echo "=== Generated documentation ==="
cat /tmp/verus-rational-docs.md
