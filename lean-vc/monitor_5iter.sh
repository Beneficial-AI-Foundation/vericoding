#!/bin/bash
# Monitor 5-iteration experiment and alert when done

echo "Monitoring 5-iteration experiment..."
echo "Started at: $(date)"
echo ""

while [ ! -f benchmarks_generated/experiment_5iter/results.csv ]; do
    FILES_DONE=$(ls benchmarks_generated/experiment_5iter/*_impl.lean 2>/dev/null | wc -l || echo 0)
    echo -ne "\rProgress: $FILES_DONE/50 files processed..."
    sleep 30
done

echo -e "\n\n5-ITERATION EXPERIMENT COMPLETE!"
echo "Completed at: $(date)"
echo ""
echo "Results Summary:"
echo "==============="
echo "Total files: $(wc -l < benchmarks_generated/experiment_5iter/results.csv)"
echo "Successful: $(grep -c ",success," benchmarks_generated/experiment_5iter/results.csv || echo 0)"
echo "Failed: $(grep -c ",failed," benchmarks_generated/experiment_5iter/results.csv || echo 0)"
echo ""

# Compare with 1-iteration results
echo "Comparison with 1-iteration:"
echo "==========================="
SUCCESS_1=$(grep -c ",success," benchmarks_generated/experiment_1iter/results.csv || echo 0)
SUCCESS_5=$(grep -c ",success," benchmarks_generated/experiment_5iter/results.csv || echo 0)
echo "1-iter success: $SUCCESS_1/50"
echo "5-iter success: $SUCCESS_5/50"
echo "Improvement: $((SUCCESS_5 - SUCCESS_1)) additional successes"

# Alert (on macOS)
if command -v terminal-notifier >/dev/null 2>&1; then
    terminal-notifier -message "5-iteration experiment complete! Success: $SUCCESS_5/50" -title "Lean Experiment"
fi