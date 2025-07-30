#!/bin/bash
# Migration helper script for transitioning to the unified spec_to_code.py

echo "=== Migration Helper for Unified spec_to_code.py ==="
echo ""
echo "This script helps you migrate from language-specific scripts to the unified script."
echo ""

# Function to show old vs new command
show_migration() {
    local lang=$1
    local old_script=$2
    local example_dir=$3
    
    echo "For $lang:"
    echo "  OLD: python $old_script $example_dir --iterations 5"
    echo "  NEW: python spec_to_code.py $lang $example_dir --iterations 5"
    echo ""
}

# Show migration examples
echo "Command Migration Examples:"
echo "--------------------------"
show_migration "Dafny" "dafny/spec_to_code.py" "./specs"
show_migration "Lean" "lean/spec_to_code_lean.py" "./NumpySpec/DafnySpecs"
show_migration "Verus" "verus/spec_to_code.py" "./benchmarks/verus_specs"

echo "Key Changes:"
echo "------------"
echo "1. Use the unified script: spec_to_code.py"
echo "2. Specify language as first argument: dafny, lean, or verus"
echo "3. All other arguments remain the same"
echo "4. Environment variables (DAFNY_PATH, LEAN_PATH, VERUS_PATH) remain unchanged"
echo "5. Prompt files remain in their current locations"
echo ""

# Check if old scripts are being used
echo "Checking for old script usage in current directory..."
echo ""

# Find shell scripts or Python files that might reference old scripts
old_references=$(grep -r "spec_to_code.py\|spec_to_code_lean.py" --include="*.sh" --include="*.py" --include="*.md" . 2>/dev/null | \
    grep -E "(dafny/spec_to_code\.py|lean/spec_to_code_lean\.py|verus/spec_to_code\.py)" | \
    grep -v "migrate_to_unified.sh" | \
    grep -v "spec_to_code.py" | \
    head -20)

if [ ! -z "$old_references" ]; then
    echo "Found references to old scripts:"
    echo "$old_references"
    echo ""
    echo "Consider updating these files to use the unified script."
else
    echo "No references to old scripts found in common file types."
fi

echo ""
echo "Quick Test Commands:"
echo "-------------------"
echo "# Test Dafny:"
echo "python spec_to_code.py dafny --help"
echo ""
echo "# Test Lean:"
echo "python spec_to_code.py lean --help"
echo ""
echo "# Test Verus:"
echo "python spec_to_code.py verus --help"
echo ""
echo "Configuration file location: config/language_config.yaml"
echo ""
echo "For more information, see README_unified_spec_to_code.md"
