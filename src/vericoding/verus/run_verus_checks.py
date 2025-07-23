import os
import subprocess
from pathlib import Path
from datetime import datetime
import json

VERUS_PATH = os.path.expanduser("~/Downloads/verus-0.2025.06.14.9b557d7-x86-linux/verus-x86-linux/verus")
SPECS_DIR = "src/verus_specs_no_llm/translations"
LOG_DIR = "logs"

def run_verus_check(file_path: Path) -> tuple[bool, str]:
    """Run Verus check on a single file and return success status and error message if any."""
    try:
        result = subprocess.run(
            [VERUS_PATH, "--no-verify", str(file_path)],
            capture_output=True,
            text=True,
            check=False
        )
        return result.returncode == 0, result.stderr if result.returncode != 0 else ""
    except Exception as e:
        return False, str(e)

def get_file_link(file_path: Path, workspace_root: Path) -> str:
    """Generate a clickable link to the file using relative path from logs directory."""
    try:
        abs_path = file_path.resolve()
        rel_path = abs_path.relative_to(workspace_root)
        return f"[{rel_path}](../{rel_path})"
    except Exception:
        return str(file_path)

def process_directory():
    """Process all Rust files in the specs directory and collect statistics."""
    specs_path = Path(SPECS_DIR)
    log_dir = Path(LOG_DIR)
    log_dir.mkdir(exist_ok=True)
    
    # Get workspace root (assuming script is run from workspace root)
    workspace_root = Path.cwd()
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = log_dir / f"verus_check_results_{timestamp}.md"
    
    total_files = 0
    successful_files = 0
    failed_files = []
    successful_files_list = []
    
    with open(log_file, "w") as log:
        log.write(f"# Verus Check Results\n\n")
        log.write(f"Generated on: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        
        # Create sections for successful and failed compilations
        log.write("## Failed Compilations\n\n")
        
        for rust_file in specs_path.rglob("*.rs"):
            total_files += 1
            file_link = get_file_link(rust_file, workspace_root)
            
            success, error_msg = run_verus_check(rust_file)
            
            if success:
                successful_files += 1
                successful_files_list.append(str(rust_file.relative_to(specs_path)))
            else:
                failed_files.append(str(rust_file.relative_to(specs_path)))
                log.write(f"### {file_link}\n\n")
                log.write("```\n")
                log.write(error_msg)
                log.write("\n```\n\n")
        
        # Add summary section at the top
        with open(log_file, "r+") as log:
            content = log.read()
            log.seek(0)
            log.write(f"# Verus Check Results\n\n")
            log.write(f"Generated on: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            
            # Write summary
            log.write("## Summary\n\n")
            success_rate = (successful_files / total_files * 100) if total_files > 0 else 0
            log.write(f"- Total files processed: {total_files}\n")
            log.write(f"- Successful compilations: {successful_files}\n")
            log.write(f"- Failed compilations: {len(failed_files)}\n")
            log.write(f"- Success rate: {success_rate:.2f}%\n\n")
            
            # Add the rest of the content
            log.write(content)
    
    # Calculate statistics
    success_rate = (successful_files / total_files * 100) if total_files > 0 else 0
    
    # Save statistics in markdown format
    stats_file = log_dir / f"verus_check_stats_{timestamp}.md"
    with open(stats_file, "w") as f:
        f.write("# Verus Check Statistics\n\n")
        f.write(f"Generated on: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        
        # Summary section
        f.write("## Summary\n\n")
        f.write(f"- Total files processed: {total_files}\n")
        f.write(f"- Successful compilations: {successful_files}\n")
        f.write(f"- Failed compilations: {len(failed_files)}\n")
        f.write(f"- Success rate: {success_rate:.2f}%\n\n")
        
        # Successful files section
        f.write("## Successful Files\n\n")
        for file_path in successful_files_list:
            link = get_file_link(specs_path / file_path, workspace_root)
            f.write(f"- {link}\n")
        f.write("\n")
        
        # Failed files section
        f.write("## Failed Files\n\n")
        for file_path in failed_files:
            link = get_file_link(specs_path / file_path, workspace_root)
            f.write(f"- {link}\n")
    
    # Print summary
    print(f"\nResults Summary:")
    print(f"Total files processed: {total_files}")
    print(f"Successful compilations: {successful_files}")
    print(f"Failed compilations: {len(failed_files)}")
    print(f"Success rate: {success_rate:.2f}%")
    print(f"\nDetailed results have been saved to: {log_file}")
    print(f"Statistics have been saved to: {stats_file}")

if __name__ == "__main__":
    process_directory()