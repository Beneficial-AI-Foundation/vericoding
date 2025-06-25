import os
import subprocess
from pathlib import Path
from datetime import datetime
import json
import sys

VERUS_PATH = os.path.expanduser("~/Downloads/verus-0.2025.06.14.9b557d7-x86-linux/verus-x86-linux/verus")
SPECS_DIR = "src/verus_specs_no_llm/translations"
LOG_DIR = "logs"

def make_clickable(file_path: str | Path) -> str:
    """Make a file path clickable in Cursor terminal."""
    # Convert to absolute path if it's not already
    abs_path = str(Path(file_path).absolute())
    # Use cursor:// protocol to open in Cursor
    return f"\x1b]8;;cursor://open?file={abs_path}\x1b\\{abs_path}\x1b]8;;\x1b\\"

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
    """Process Rust files in the specs directory until first failure."""
    specs_path = Path(SPECS_DIR)
    log_dir = Path(LOG_DIR)
    log_dir.mkdir(exist_ok=True)
    
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    log_file = log_dir / f"verus_check_fail_fast_results_{timestamp}.txt"
    
    total_files = 0
    successful_files = 0
    
    with open(log_file, "w") as log:
        log.write(f"Verus Check Results (Fail Fast Mode) - {datetime.now()}\n")
        log.write("=" * 80 + "\n\n")
        
        try:
            for rust_file in specs_path.rglob("*.rs"):
                total_files += 1
                relative_path = rust_file.relative_to(specs_path)
                
                log.write(f"Checking {relative_path}...\n")
                success, error_msg = run_verus_check(rust_file)
                
                if success:
                    successful_files += 1
                    log.write("✓ Success\n\n")
                else:
                    log.write("✗ Failed\n")
                    log.write("-" * 40 + "\n")
                    log.write(error_msg)
                    log.write("\n" + "-" * 40 + "\n\n")
                    
                    # Print failure information to console with clickable path
                    print(f"\n❌ First failure encountered in file: {make_clickable(rust_file)}")
                    print("\nError message:")
                    print("-" * 40)
                    print(error_msg)
                    print("-" * 40)
                    
                    # Save summary statistics before exiting
                    success_rate = (successful_files / total_files * 100)
                    log.write(f"\nSummary before stopping:\n")
                    log.write(f"Files processed before failure: {total_files}\n")
                    log.write(f"Successful compilations: {successful_files}\n")
                    log.write(f"Success rate before failure: {success_rate:.2f}%\n")
                    
                    print(f"\nResults Summary:")
                    print(f"Files processed before failure: {total_files}")
                    print(f"Successful compilations: {successful_files}")
                    print(f"Success rate before failure: {success_rate:.2f}%")
                    print(f"\nDetailed results have been saved to: {make_clickable(log_file)}")
                    
                    sys.exit(1)  # Exit with error code
        
        except KeyboardInterrupt:
            log.write("\nProcess interrupted by user.\n")
            print("\nProcess interrupted by user.")
            sys.exit(2)
    
    # If we get here, all files succeeded
    success_rate = 100.0
    log.write(f"\nAll files compiled successfully!\n")
    log.write(f"Total files processed: {total_files}\n")
    log.write(f"Success rate: {success_rate}%\n")
    
    print(f"\nResults Summary:")
    print(f"All {total_files} files compiled successfully!")
    print(f"\nDetailed results have been saved to: {make_clickable(log_file)}")

if __name__ == "__main__":
    process_directory() 