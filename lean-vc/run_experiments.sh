#!/bin/bash
# Run both experiments sequentially

echo "Starting experiments..."
echo "======================"

# Wait for 1-iteration experiment to complete
echo "Waiting for 1-iteration experiment to complete..."
while ps aux | grep -q "[s]pec_to_code.*experiment_1iter"; do
    sleep 10
done

echo "1-iteration experiment completed!"
if [ -f benchmarks_generated/experiment_1iter/results.csv ]; then
    echo "Results saved to benchmarks_generated/experiment_1iter/results.csv"
    echo "Success count: $(grep -c ",True," benchmarks_generated/experiment_1iter/results.csv || echo 0)"
fi

# Start 5-iteration experiment
echo ""
echo "Starting 5-iteration experiment..."
./spec_to_code_lean.py experiment_run/specs --iterations 5 --output-dir benchmarks_generated/experiment_5iter --api-delay 1.5 > experiment_5iter_full.log 2>&1 &
PID5=$!
echo "Started 5-iteration experiment with PID: $PID5"

# Monitor 5-iteration experiment
echo "Monitoring 5-iteration experiment..."
while ps aux | grep -q "$PID5"; do
    if [ -f benchmarks_generated/experiment_5iter/results.csv ]; then
        PROCESSED=$(wc -l < benchmarks_generated/experiment_5iter/results.csv 2>/dev/null || echo 0)
        echo -ne "\rFiles processed: $PROCESSED/50"
    fi
    sleep 10
done

echo -e "\n5-iteration experiment completed!"
if [ -f benchmarks_generated/experiment_5iter/results.csv ]; then
    echo "Results saved to benchmarks_generated/experiment_5iter/results.csv"
    echo "Success count: $(grep -c ",True," benchmarks_generated/experiment_5iter/results.csv || echo 0)"
fi

echo ""
echo "Both experiments completed! Ready for analysis."