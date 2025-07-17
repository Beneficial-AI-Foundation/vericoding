import os
import subprocess
from pathlib import Path
from datetime import datetime
import json
import sys

# Get the absolute path to the script's directory
SCRIPT_DIR = Path(__file__).parent.absolute()
WORKSPACE_ROOT = SCRIPT_DIR.parent.parent  # Go up two levels to reach workspace root

VERUS_PATH = os.path.expanduser("~/Downloads/verus-0.2025.06.14.9b557d7-x86-linux/verus-x86-linux/verus")
SPECS_DIR = SCRIPT_DIR / "verus_specs_no_llm/translations"
LOG_DIR = WORKSPACE_ROOT / "logs"
DAFNY_BENCHMARKS_DIR = WORKSPACE_ROOT / "dafny/benchmarks"  # Now using absolute path

def make_clickable(file_path: str | Path) -> str:
    """Make a file path clickable in Cursor terminal."""
    # Convert to absolute path if it's not already
    abs_path = str(Path(file_path).absolute())
    # Use cursor:// protocol to open in Cursor
    return f"\x1b]8;;cursor://open?file={abs_path}\x1b\\{abs_path}\x1b]8;;\x1b\\"

def make_relative_to_logs(file_path: Path) -> Path:
    """Convert a path to be relative to the logs directory."""
    try:
        # First make both paths absolute to handle any relative paths correctly
        abs_file_path = file_path.absolute()
        abs_log_dir = LOG_DIR.absolute()
        # Go up one level from logs and then make relative
        return abs_file_path.relative_to(abs_log_dir.parent)
    except ValueError:
        # If we can't make it relative, return the original path
        return file_path

def make_md_link(file_path: Path) -> str:
    """Create a markdown link for a file."""
    relative_path = make_relative_to_logs(file_path)
    # Add ../ to make the path relative from the logs directory
    return f"[{file_path.name}](../{relative_path})"

def find_original_dafny_file(verus_file: Path) -> tuple[Path | None, list[str]]:
    """Find the original Dafny file that was translated to this Verus file."""
    debug_info = []
    # Get the relative path from the translations directory
    relative_path = verus_file.relative_to(SPECS_DIR)
    
    # Replace .rs extension with .dfy
    dafny_name = relative_path.stem + ".dfy"
    
    debug_info.append("### Search Locations")
    # Look in corresponding directories in the Dafny benchmarks
    possible_locations = [
        DAFNY_BENCHMARKS_DIR / "dafny-bench_specs" / relative_path.parent / dafny_name,
        # Add more potential locations if needed
    ]
    
    for loc in possible_locations:
        exists = loc.exists()
        relative_loc = make_relative_to_logs(loc)
        debug_info.append(f"- Checking: `../{relative_loc}`")
        debug_info.append(f"  - Exists: {'✓' if exists else '✗'}")
        if exists:
            return loc, debug_info
    return None, debug_info

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
    log_file = log_dir / f"verus_check_fail_fast_results_{timestamp}.md"
    
    total_files = 0
    successful_files = 0
    
    with open(log_file, "w") as log:
        log.write(f"# Verus Check Results (Fail Fast Mode)\n\n")
        log.write(f"**Run Date:** {datetime.now()}\n\n")
        log.write("---\n\n")
        
        try:
            for rust_file in specs_path.rglob("*.rs"):
                total_files += 1
                relative_path = rust_file.relative_to(specs_path)
                
                log.write(f"## Checking {relative_path}\n\n")
                success, error_msg = run_verus_check(rust_file)
                
                if success:
                    successful_files += 1
                    log.write("✓ Success\n\n")
                else:
                    log.write("✗ Failed\n\n")
                    log.write("### Error Message\n")
                    log.write("```\n")
                    log.write(error_msg)
                    log.write("\n```\n\n")
                    
                    # Find original Dafny file
                    original_dafny, debug_info = find_original_dafny_file(rust_file)
                    
                    # Write debug info to markdown
                    log.write("### File Information\n")
                    log.write(f"- **Verus File:** {make_md_link(rust_file)}\n")
                    if original_dafny:
                        log.write(f"- **Original Dafny File:** {make_md_link(original_dafny)}\n")
                    else:
                        log.write("- **Original Dafny File:** Not found\n")
                    log.write("\n")
                    
                    # Write debug info
                    log.write("\n".join(debug_info))
                    log.write("\n\n")
                    
                    # Print to console with clickable paths
                    print(f"\n❌ First failure encountered in file: {make_clickable(rust_file)}")
                    if original_dafny:
                        print(f"Original Dafny file: {make_clickable(original_dafny)}")
                    else:
                        print("Original Dafny file not found")
                    print("\nError message:")
                    print("-" * 40)
                    print(error_msg)
                    print("-" * 40)
                    
                    # Save summary statistics before exiting
                    success_rate = (successful_files / total_files * 100)
                    log.write("## Summary Before Failure\n\n")
                    log.write(f"- Files processed before failure: {total_files}\n")
                    log.write(f"- Successful compilations: {successful_files}\n")
                    log.write(f"- Success rate before failure: {success_rate:.2f}%\n")
                    
                    print(f"\nResults Summary:")
                    print(f"Files processed before failure: {total_files}")
                    print(f"Successful compilations: {successful_files}")
                    print(f"Success rate before failure: {success_rate:.2f}%")
                    print(f"\nDetailed results have been saved to: {make_clickable(log_file)}")
                    
                    sys.exit(1)  # Exit with error code
        
        except KeyboardInterrupt:
            log.write("\n## Process Interrupted\n\n")
            log.write("Process was interrupted by user.\n")
            print("\nProcess interrupted by user.")
            sys.exit(2)
    
    # If we get here, all files succeeded
    success_rate = 100.0
    log.write("## Final Summary\n\n")
    log.write("✓ All files compiled successfully!\n\n")
    log.write(f"- Total files processed: {total_files}\n")
    log.write(f"- Success rate: {success_rate}%\n")
    
    print(f"\nResults Summary:")
    print(f"All {total_files} files compiled successfully!")
    print(f"\nDetailed results have been saved to: {make_clickable(log_file)}")

if __name__ == "__main__":
    process_directory() 