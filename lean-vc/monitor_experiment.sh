#!/bin/bash
# Monitor experiment progress

echo "Monitoring spec_to_code experiment..."
echo "=====================================\n"

while true; do
    clear
    echo "Experiment Progress Monitor"
    echo "==========================="
    date
    echo ""
    
    # Check 1-iteration experiment
    if ps aux | grep -q "[s]pec_to_code.*experiment_1iter"; then
        echo "✓ 1-iteration experiment: RUNNING"
        if [ -f benchmarks_generated/experiment_1iter/results.csv ]; then
            echo "  Files processed: $(wc -l < benchmarks_generated/experiment_1iter/results.csv)"
        fi
    else
        echo "✗ 1-iteration experiment: COMPLETED or NOT RUNNING"
    fi
    
    # Check 5-iteration experiment
    if ps aux | grep -q "[s]pec_to_code.*experiment_5iter"; then
        echo "✓ 5-iteration experiment: RUNNING"
        if [ -f benchmarks_generated/experiment_5iter/results.csv ]; then
            echo "  Files processed: $(wc -l < benchmarks_generated/experiment_5iter/results.csv)"
        fi
    else
        echo "✗ 5-iteration experiment: NOT STARTED or COMPLETED"
    fi
    
    echo ""
    echo "Generated files:"
    echo "1-iter: $(ls benchmarks_generated/experiment_1iter/*_impl.lean 2>/dev/null | wc -l) implementations"
    echo "5-iter: $(ls benchmarks_generated/experiment_5iter/*_impl.lean 2>/dev/null | wc -l) implementations"
    
    echo ""
    echo "Press Ctrl+C to exit..."
    sleep 10
done