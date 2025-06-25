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

def process_directory():
    """Process all Rust files in the specs directory and collect statistics."""
    specs_path = Path(SPECS_DIR)
    log_dir = Path(LOG_DIR)
    log_dir.mkdir(exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = log_dir / f"verus_check_results_{timestamp}.txt"
    stats_file = log_dir / f"verus_check_stats_{timestamp}.json"
    
    total_files = 0
    successful_files = 0
    failed_files = []
    
    with open(log_file, "w") as log:
        log.write(f"Verus Check Results - {datetime.now()}\n")
        log.write("=" * 80 + "\n\n")
        
        for rust_file in specs_path.rglob("*.rs"):
            total_files += 1
            relative_path = rust_file.relative_to(specs_path)
            
            log.write(f"Checking {relative_path}...\n")
            success, error_msg = run_verus_check(rust_file)
            
            if success:
                successful_files += 1
                log.write("✓ Success\n\n")
            else:
                failed_files.append(str(relative_path))
                log.write("✗ Failed\n")
                log.write("-" * 40 + "\n")
                log.write(error_msg)
                log.write("\n" + "-" * 40 + "\n\n")
    
    # Calculate statistics
    success_rate = (successful_files / total_files * 100) if total_files > 0 else 0
    stats = {
        "timestamp": timestamp,
        "total_files": total_files,
        "successful_files": successful_files,
        "failed_files": failed_files,
        "success_rate": round(success_rate, 2)
    }
    
    # Save statistics
    with open(stats_file, "w") as f:
        json.dump(stats, f, indent=2)
    
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