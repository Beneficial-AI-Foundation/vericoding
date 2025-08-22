#!/usr/bin/env python3
"""
Process verified-cogen repository: clone, convert Rust files to YAML, and maintain directory structure.
DRY version that reuses existing code.
"""

import json
import tempfile
import uuid
import shutil
from pathlib import Path
from typing import List
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


def convert_rust_files_to_yaml(rust_files: List[RustFile], output_dir: Path) -> None:
    """Convert Rust files to YAML format and write to output directory with same structure."""
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
    parser.add_argument("--no-cleanup", action="store_true", help="Don't clean up the cloned repository")
    
    args = parser.parse_args()
    
    # Set up output directory
    if args.output_dir:
        output_dir = Path(args.output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
    else:
        temp_base = Path(tempfile.gettempdir())
        output_dir = temp_base / f"verified-cogen-yaml-{uuid.uuid4().hex[:8]}"
        output_dir.mkdir(parents=True, exist_ok=True)
        
    print(f"📂 Output directory: {output_dir}")
    
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
        
        # Step 5: Convert to YAML (new functionality)
        print("⚡ Step 5: Converting to YAML...")
        convert_rust_files_to_yaml(rust_files, output_dir)
        
        # Step 6: Create summary report (new functionality)
        print("📊 Step 6: Creating summary report...")
        create_summary_report(rust_files, output_dir)
        
        print(f"\n🎉 Process completed successfully!")
        print(f"📂 YAML files written to: {output_dir}")
        
    finally:
        # Clean up cloned repository
        if not args.no_cleanup and clone_temp_dir.exists():
            shutil.rmtree(clone_temp_dir)
            print(f"🧹 Cleaned up temporary directory: {clone_temp_dir}")


if __name__ == "__main__":
    main()