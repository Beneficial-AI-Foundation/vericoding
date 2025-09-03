#!/bin/bash

# Simplified test script for dafny/dafnybench consistency

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

log_info() { echo -e "${GREEN}[INFO]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

main() {
    log_info "Testing conversion consistency for dafny/dafnybench..."
    
    local benchmark_path="benchmarks/dafny/dafnybench"
    local yaml_dir="$benchmark_path/yaml"
    local files_dir="$benchmark_path/files"
    local jsonl_file="$benchmark_path/dafny_dafnybench.jsonl"
    local generated_dir="$yaml_dir"_dfy
    
    # Count files
    local yaml_count=$(find "$yaml_dir" -name "*.yaml" | wc -l)
    local files_count=$(find "$files_dir" -name "*.dfy" | wc -l)
    local jsonl_entries=$(wc -l < "$jsonl_file")
    
    log_info "YAML files: $yaml_count"
    log_info "Generated files (.dfy): $files_count" 
    log_info "JSONL entries: $jsonl_entries"
    
    # Test file counts
    if [[ $yaml_count -eq $files_count && $files_count -eq $jsonl_entries ]]; then
        log_info "✓ All file counts match exactly: $yaml_count files"
    else
        log_error "✗ File counts do not match"
        exit 1
    fi
    
    # Initialize failed flag
    local failed=false
    
    # Test JSONL consistency using temp directory
    log_info "Testing JSONL consistency..."
    local temp_dir=$(mktemp -d)
    local temp_yaml="$temp_dir/yaml"
    cp -r "$yaml_dir" "$temp_yaml"
    
    if uv run src/convert_from_yaml.py "$temp_yaml" --suffix jsonl >/dev/null 2>&1; then
        local generated_jsonl="$temp_yaml.jsonl"
        
        if [[ -f "$generated_jsonl" ]]; then
            if ! diff -q "$generated_jsonl" "$jsonl_file" >/dev/null 2>&1; then
                log_error "✗ JSONL file does not match YAML conversion"
                failed=true
            else
                log_info "✓ JSONL file matches YAML conversion"
            fi
        else
            log_error "Failed to generate JSONL file"
            failed=true
        fi
    else
        log_error "Failed to convert YAML to JSONL"
        failed=true
    fi
    
    # Test file differences using temp directory
    log_info "Testing file consistency..."
    local temp_yaml2="$temp_dir/yaml2"
    cp -r "$yaml_dir" "$temp_yaml2"
    
    # Find differing files
    local differing_files=()
    
    if uv run src/convert_from_yaml.py "$temp_yaml2" --suffix dfy --dir >/dev/null 2>&1; then
        local temp_generated_dir="$temp_yaml2"_dfy
        
        if [[ -d "$temp_generated_dir" ]]; then
            log_info "Comparing files..."
            
            for f in "$temp_generated_dir"/*.dfy; do
                local basename_f=$(basename "$f")
                local existing_file="$files_dir/$basename_f"
                
                if [[ ! -f "$existing_file" ]]; then
                    log_error "Missing file: $basename_f"
                    failed=true
                elif ! diff -q "$f" "$existing_file" >/dev/null 2>&1; then
                    differing_files+=("$basename_f")
                    failed=true
                fi
            done
        else
            log_error "Failed to generate files from YAML"
            failed=true
        fi
    else
        log_error "Failed to convert YAML to files"
        failed=true
    fi
    
    # Cleanup temp directory
    rm -rf "$temp_dir"
    
    # Report final results
    if [[ ${#differing_files[@]} -gt 0 ]]; then
        log_error "✗ Found ${#differing_files[@]} differing files:"
        for file in "${differing_files[@]}"; do
            log_error "  - $file"
        done
        failed=true
    else
        log_info "✓ All files match exactly"
    fi
    
    # Final summary
    if [[ "$failed" == "true" ]]; then
        log_error "✗ Tests failed!"
        exit 1
    else
        log_info "✓ All consistency tests passed!"
        exit 0
    fi
}

main "$@"