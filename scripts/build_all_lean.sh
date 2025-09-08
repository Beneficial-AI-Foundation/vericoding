#!/bin/bash

# Build all Lean files from a folder with status tracking and error logging
# Usage: ./build_all_lean.sh <folder_path> [output_dir]

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Default values
FOLDER_PATH="${1:-}"
OUTPUT_DIR="${2:-build_logs}"
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
LOG_DIR="${OUTPUT_DIR}/${TIMESTAMP}"

# Help function
show_help() {
    echo "Usage: $0 <folder_path> [output_dir]"
    echo ""
    echo "Build all .lean files in a folder with comprehensive logging"
    echo ""
    echo "Arguments:"
    echo "  folder_path   Path to folder containing .lean files"
    echo "  output_dir    Output directory for logs (default: build_logs)"
    echo ""
    echo "Examples:"
    echo "  $0 benchmarks/lean/humaneval/files"
    echo "  $0 lean/Generated/Run_08-09_11h21/first10 my_logs"
}

# Check arguments
if [[ -z "$FOLDER_PATH" ]] || [[ "$FOLDER_PATH" == "-h" ]] || [[ "$FOLDER_PATH" == "--help" ]]; then
    show_help
    exit 0
fi

if [[ ! -d "$FOLDER_PATH" ]]; then
    echo -e "${RED}Error: Directory '$FOLDER_PATH' does not exist${NC}"
    exit 1
fi

# Create log directory
mkdir -p "$LOG_DIR"

# Find all .lean files
echo -e "${BLUE}Scanning for .lean files in: $FOLDER_PATH${NC}"
LEAN_FILES=($(find "$FOLDER_PATH" -name "*.lean" | sort))
TOTAL_FILES=${#LEAN_FILES[@]}

if [[ $TOTAL_FILES -eq 0 ]]; then
    echo -e "${YELLOW}No .lean files found in $FOLDER_PATH${NC}"
    exit 0
fi

echo -e "${BLUE}Found $TOTAL_FILES .lean files${NC}"

# Initialize counters and logs
SUCCESS_COUNT=0
FAILED_COUNT=0
WARNING_COUNT=0
SUCCESS_LOG="$LOG_DIR/successful_builds.log"
FAILED_LOG="$LOG_DIR/failed_builds.log"
WARNING_LOG="$LOG_DIR/builds_with_warnings.log"
SUMMARY_LOG="$LOG_DIR/build_summary.log"
DETAILED_LOG="$LOG_DIR/detailed_build.log"

# Initialize log files
echo "Build started at $(date)" > "$SUMMARY_LOG"
echo "Folder: $FOLDER_PATH" >> "$SUMMARY_LOG"
echo "Total files: $TOTAL_FILES" >> "$SUMMARY_LOG"
echo "" >> "$SUMMARY_LOG"

echo "=== SUCCESSFUL BUILDS ===" > "$SUCCESS_LOG"
echo "=== FAILED BUILDS ===" > "$FAILED_LOG"
echo "=== BUILDS WITH WARNINGS ===" > "$WARNING_LOG"
echo "=== DETAILED BUILD LOG ===" > "$DETAILED_LOG"

# Progress bar function
show_progress() {
    local current=$1
    local total=$2
    local width=50
    local percentage=$((current * 100 / total))
    local completed=$((current * width / total))
    local remaining=$((width - completed))
    
    printf "\rProgress: ["
    printf "%${completed}s" | tr ' ' '='
    printf "%${remaining}s" | tr ' ' '-'
    printf "] %d/%d (%d%%)" "$current" "$total" "$percentage"
}

echo -e "\n${BLUE}Starting build process...${NC}\n"

# Build each file
for i in "${!LEAN_FILES[@]}"; do
    file="${LEAN_FILES[$i]}"
    filename=$(basename "$file")
    current=$((i + 1))
    
    show_progress "$current" "$TOTAL_FILES"
    
    # Log the attempt
    echo "" >> "$DETAILED_LOG"
    echo "[$current/$TOTAL_FILES] Building: $file" >> "$DETAILED_LOG"
    echo "Time: $(date)" >> "$DETAILED_LOG"
    
    # Run lake build and capture output
    if build_output=$(lake build "$file" 2>&1); then
        if echo "$build_output" | grep -q "warning:"; then
            # Success but with warnings
            WARNING_COUNT=$((WARNING_COUNT + 1))
            echo "$file" >> "$WARNING_LOG"
            echo "  Warnings found:" >> "$WARNING_LOG"
            echo "$build_output" | grep "warning:" | sed 's/^/    /' >> "$WARNING_LOG"
            echo "" >> "$WARNING_LOG"
            
            echo "SUCCESS (with warnings): $file" >> "$DETAILED_LOG"
        else
            # Clean success
            SUCCESS_COUNT=$((SUCCESS_COUNT + 1))
            echo "$file" >> "$SUCCESS_LOG"
            echo "SUCCESS: $file" >> "$DETAILED_LOG"
        fi
        echo "$build_output" >> "$DETAILED_LOG"
    else
        # Build failed
        FAILED_COUNT=$((FAILED_COUNT + 1))
        echo "$file" >> "$FAILED_LOG"
        echo "  Error:" >> "$FAILED_LOG"
        echo "$build_output" | sed 's/^/    /' >> "$FAILED_LOG"
        echo "" >> "$FAILED_LOG"
        
        echo "FAILED: $file" >> "$DETAILED_LOG"
        echo "$build_output" >> "$DETAILED_LOG"
    fi
    
    echo "---" >> "$DETAILED_LOG"
done

# Clear progress line and show final results
printf "\r%*s\r" 80 ""

echo -e "\n${BLUE}Build Summary:${NC}"
echo -e "${GREEN}✓ Successful: $SUCCESS_COUNT${NC}"
echo -e "${YELLOW}⚠ With warnings: $WARNING_COUNT${NC}"
echo -e "${RED}✗ Failed: $FAILED_COUNT${NC}"
echo -e "${BLUE}📁 Logs saved to: $LOG_DIR${NC}"

# Update summary log
{
    echo ""
    echo "=== FINAL SUMMARY ==="
    echo "Build completed at: $(date)"
    echo "Total files processed: $TOTAL_FILES"
    echo "Successful builds: $SUCCESS_COUNT"
    echo "Builds with warnings: $WARNING_COUNT"
    echo "Failed builds: $FAILED_COUNT"
    echo ""
    echo "Success rate: $(( (SUCCESS_COUNT + WARNING_COUNT) * 100 / TOTAL_FILES ))%"
} >> "$SUMMARY_LOG"

# Show top failed files if any
if [[ $FAILED_COUNT -gt 0 ]]; then
    echo -e "\n${RED}Top failed files:${NC}"
    head -10 "$FAILED_LOG" | grep -v "=== FAILED BUILDS ===" | grep "\.lean$" | head -5
    
    if [[ $FAILED_COUNT -gt 5 ]]; then
        echo -e "${YELLOW}... and $((FAILED_COUNT - 5)) more (see $FAILED_LOG)${NC}"
    fi
fi

# Show warnings summary if any
if [[ $WARNING_COUNT -gt 0 ]]; then
    echo -e "\n${YELLOW}Files with warnings: $WARNING_COUNT (see $WARNING_LOG)${NC}"
fi

echo -e "\n${BLUE}Detailed logs available in:${NC}"
echo -e "  📋 Summary: $SUMMARY_LOG"
echo -e "  ✅ Successful: $SUCCESS_LOG"
echo -e "  ⚠️  Warnings: $WARNING_LOG"
echo -e "  ❌ Failed: $FAILED_LOG"
echo -e "  📝 Detailed: $DETAILED_LOG"

# Exit with appropriate code
if [[ $FAILED_COUNT -gt 0 ]]; then
    exit 1
else
    exit 0
fi
