#!/usr/bin/env python3
"""
Process verified-cogen repository: clone, convert Rust files to YAML, and maintain directory structure.
DRY version that reuses existing code.
"""

from tqdm import tqdm
import json
import tempfile
import uuid
import shutil
import subprocess
from pathlib import Path
from typing import List, Tuple
import argparse

# Import our existing functionality - DRY!
from clone_verified_cogen_rs import (
    RustFile, 
    clone_repo, 
    find_rust_files, 
    read_rust_files, 
    filter_duplicates
)
from rust_to_yaml_converter import rust_to_yaml
from verus_validation import (
    find_verus_executable, 
    verify_rust_with_verus, 
    create_yaml_without_helpers,
    validate_yaml_with_verus,
    VerusNotFoundError
)



def convert_and_filter_rust_files_to_yaml(rust_files: List[RustFile], output_dir: Path, filtered_dir: Path, log_path: Path) -> None:
    """Convert Rust files to YAML format and filter based on Verus validation."""
    # Find Verus executable - will raise VerusNotFoundError if not found
    verus_cmd = find_verus_executable()
    
    print(f"✅ Found Verus at: {verus_cmd}")
    print("🔄 Converting and filtering files based on Verus validation...")
    
    successful_conversions = 0
    failed_conversions = []
    filtered_out = []
    
    # Create temp directory for validation
    with tempfile.TemporaryDirectory(prefix="verus_filter_") as temp_dir:
        temp_path = Path(temp_dir)
        
        for i, rust_file in tqdm(enumerate(rust_files)):
            if (i + 1) % 50 == 0:
                print(f"Processing {i+1}/{len(rust_files)} files...")
            
            try:
                # Convert Rust content to YAML
                yaml_content = rust_to_yaml(rust_file.content)
                
                # Validate with Verus
                original_valid, no_helpers_valid, error_msg = validate_yaml_with_verus(
                    yaml_content, verus_cmd, temp_path
                )
                
                # Determine output path
                output_path = output_dir / Path(rust_file.path).with_suffix('.yaml')
                
                if original_valid and no_helpers_valid:
                    # File passes validation - include in main output
                    output_path.parent.mkdir(parents=True, exist_ok=True)
                    with open(output_path, 'w', encoding='utf-8') as f:
                        f.write(yaml_content)
                    successful_conversions += 1
                    
                    # Also copy to filtered directory
                    filtered_path = filtered_dir / Path(rust_file.path).with_suffix('.yaml')
                    filtered_path.parent.mkdir(parents=True, exist_ok=True)
                    with open(filtered_path, 'w', encoding='utf-8') as f:
                        f.write(yaml_content)
                else:
                    # File fails validation - log it
                    filter_reason = f"original_valid={original_valid}, no_helpers_valid={no_helpers_valid}, error={error_msg}"
                    filtered_out.append({
                        "path": rust_file.path,
                        "reason": filter_reason
                    })
                    
                    # Still write to main output for debugging
                    output_path.parent.mkdir(parents=True, exist_ok=True)
                    with open(output_path, 'w', encoding='utf-8') as f:
                        f.write(yaml_content)
                        
            except Exception as e:
                error_msg = f"Failed to convert {rust_file.path}: {e}"
                failed_conversions.append(error_msg)
                filtered_out.append({
                    "path": rust_file.path,
                    "reason": f"Conversion failed: {e}"
                })
                continue
    
    # Write filter log
    with open(log_path, 'w', encoding='utf-8') as f:
        json.dump({
            "filtered_out_count": len(filtered_out),
            "successful_count": successful_conversions,
            "failed_conversions_count": len(failed_conversions),
            "filtered_files": filtered_out,
            "failed_conversions": failed_conversions[:20]  # Limit to first 20
        }, f, indent=2, ensure_ascii=False)
    
    print(f"\n✅ Successfully converted and validated {successful_conversions} files")
    print(f"🚫 Filtered out {len(filtered_out)} files")
    print(f"❌ Failed to convert {len(failed_conversions)} files")
    print(f"📋 Filter log written to: {log_path}")
    
    if failed_conversions:
        print("❌ First few conversion failures:")
        for error in failed_conversions[:5]:
            print(f"  - {error}")


def convert_rust_files_to_yaml(rust_files: List[RustFile], output_dir: Path) -> None:
    """Convert Rust files to YAML format and write to output directory with same structure (no filtering)."""
    successful_conversions = 0
    failed_conversions = []
    
    for rust_file in rust_files:
        try:
            # Convert Rust content to YAML
            yaml_content = rust_to_yaml(rust_file.content)
            
            # Create output path with same directory structure, but .yaml extension
            output_path = output_dir / Path(rust_file.path).with_suffix('.yaml')
            
            # Create parent directories if they don't exist
            output_path.parent.mkdir(parents=True, exist_ok=True)
            
            # Write YAML file
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(yaml_content)
            
            successful_conversions += 1
            if successful_conversions % 50 == 0:
                print(f"Converted {successful_conversions} files...")
                
        except Exception as e:
            error_msg = f"Failed to convert {rust_file.path}: {e}"
            print(error_msg)
            failed_conversions.append(error_msg)
            continue
    
    print(f"\n✅ Successfully converted {successful_conversions} files")
    if failed_conversions:
        print(f"❌ Failed to convert {len(failed_conversions)} files:")
        for error in failed_conversions[:10]:  # Show first 10 errors
            print(f"  - {error}")
        if len(failed_conversions) > 10:
            print(f"  ... and {len(failed_conversions) - 10} more")


def create_summary_report(rust_files: List[RustFile], output_dir: Path) -> None:
    """Create a summary report of the conversion process."""
    summary = {
        "total_files": len(rust_files),
        "directories": {},
        "file_sizes": {
            "small": 0,    # < 1KB
            "medium": 0,   # 1KB - 10KB
            "large": 0,    # > 10KB
        }
    }
    
    # Analyze directory structure and file sizes
    for rust_file in rust_files:
        directory = str(Path(rust_file.path).parent)
        if directory not in summary["directories"]:
            summary["directories"][directory] = 0
        summary["directories"][directory] += 1
        
        # Categorize by content size
        content_size = len(rust_file.content)
        if content_size < 1024:
            summary["file_sizes"]["small"] += 1
        elif content_size < 10240:
            summary["file_sizes"]["medium"] += 1
        else:
            summary["file_sizes"]["large"] += 1
    
    # Write summary report
    summary_path = output_dir / "conversion_summary.json"
    with open(summary_path, 'w', encoding='utf-8') as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    
    print(f"📊 Summary report written to: {summary_path}")
    print(f"📁 Found files in {len(summary['directories'])} directories")
    print(f"📏 File sizes: {summary['file_sizes']['small']} small, {summary['file_sizes']['medium']} medium, {summary['file_sizes']['large']} large")


def main():
    """Main function to orchestrate the entire process."""
    parser = argparse.ArgumentParser(description="Process verified-cogen repository and convert to YAML")
    parser.add_argument("--output-dir", "-o", help="Output directory for YAML files (default: temp directory)")
    parser.add_argument("--keep-duplicates", action="store_true", help="Don't filter duplicate files")
    parser.add_argument("--cleanup", action="store_true", help="Clean up the cloned repository (default: keep it)")
    parser.add_argument("--no-filter", action="store_true", help="Skip Verus validation filtering")
    
    args = parser.parse_args()
    
    # Set up output directory
    if args.output_dir:
        output_dir = Path(args.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
    else:
        temp_base = Path(tempfile.gettempdir())
        output_dir = temp_base / f"verified-cogen-yaml-{uuid.uuid4().hex[:8]}"
        output_dir.mkdir(parents=True, exist_ok=True)
    
    # Set up filtered output directory
    filtered_dir = output_dir / "filtered"
    filtered_dir.mkdir(parents=True, exist_ok=True)
    
    # Set up log file path
    filter_log_path = output_dir / "filter_log.json"
        
    print(f"📂 Output directory: {output_dir}")
    print(f"📁 Filtered output directory: {filtered_dir}")
    print(f"📋 Filter log: {filter_log_path}")
    
    # Create temporary directory for cloning
    clone_temp_dir = Path(tempfile.gettempdir()) / f"verified-cogen-clone-{uuid.uuid4().hex[:8]}"
    
    try:
        # Step 1: Clone repository (reuse existing function)
        print("🔄 Step 1: Cloning repository...")
        repo_url = "https://github.com/JetBrains-Research/verified-cogen"
        repo_path = clone_repo(repo_url, clone_temp_dir)
        
        # Step 2: Find Rust files (reuse existing function)
        print("🔍 Step 2: Finding Rust files...")
        benches_dir = repo_path / "benches"
        rust_files_paths = find_rust_files(benches_dir)
        
        # Step 3: Read file contents (reuse existing function)
        print("📖 Step 3: Reading file contents...")
        rust_files = read_rust_files(rust_files_paths, repo_path)
        
        # Step 4: Filter duplicates (reuse existing function)
        if not args.keep_duplicates:
            print("🔧 Step 4: Filtering duplicates...")
            rust_files = filter_duplicates(rust_files)
        else:
            print("⏭️  Step 4: Skipping duplicate filtering")
        
        # Step 5: Convert to YAML with optional filtering
        if args.no_filter:
            print("⚡ Step 5: Converting to YAML (no filtering)...")
            convert_rust_files_to_yaml(rust_files, output_dir)
        else:
            print("⚡ Step 5: Converting to YAML with Verus validation filtering...")
            convert_and_filter_rust_files_to_yaml(rust_files, output_dir, filtered_dir, filter_log_path)
        
        # Step 6: Create summary report (new functionality)
        print("📊 Step 6: Creating summary report...")
        create_summary_report(rust_files, output_dir)
        
        print(f"\n🎉 Process completed successfully!")
        print(f"📂 All YAML files written to: {output_dir}")
        if not args.no_filter:
            print(f"✅ Validated YAML files written to: {filtered_dir}")
            print(f"📋 Filtering log available at: {filter_log_path}")
            print("\n💡 To copy filtered files elsewhere:")
            print(f"   cp -r {filtered_dir}/* /your/destination/directory/")
        
    finally:
        # Clean up cloned repository only if requested
        if args.cleanup and clone_temp_dir.exists():
            shutil.rmtree(clone_temp_dir)
            print(f"🧹 Cleaned up temporary directory: {clone_temp_dir}")
        else:
            print(f"📁 Cloned repository preserved at: {clone_temp_dir}")


if __name__ == "__main__":
    main()
