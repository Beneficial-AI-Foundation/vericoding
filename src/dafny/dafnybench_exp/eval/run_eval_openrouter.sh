#!/bin/bash

export PATH=$DAFNYBENCH_ROOT:$PATH
export TEST_SET_DIR=$DAFNYBENCH_ROOT/DafnyBench/dataset/hints_removed


sleep 0.1

source $DAFNYBENCH_ROOT/stats/bin/activate

# Parse optional range flags: --start-id and --end-id
START_ID_ARG="${START_ID}"
END_ID_ARG="${END_ID}"
while [ $# -gt 0 ]; do
    case "$1" in
        --start-id)
            START_ID_ARG="$2"; shift 2 ;;
        --start-id=*)
            START_ID_ARG="${1#*=}"; shift ;;
        --end-id)
            END_ID_ARG="$2"; shift 2 ;;
        --end-id=*)
            END_ID_ARG="${1#*=}"; shift ;;
        *)
            # ignore unknown args to keep backward compatibility
            shift ;;
    esac
done

mkdir -p ../results/results_summary
if [ ! -f "../results/results_summary/${model_to_eval}_results.csv" ]; then
    echo "test_ID,test_file,success_on_attempt_#" > "../results/results_summary/${model_to_eval}_results.csv"
fi

mkdir -p ../results/reconstructed_files
outputs_file="../results/reconstructed_files/${model_to_eval}_outputs.json"
if [ ! -f "$outputs_file" ]; then
    echo "{}" > "$outputs_file"
fi

# Set up logging
mkdir -p "$LOG_DIR"
log_file="$LOG_DIR/${model_to_eval}_$(date +%Y%m%d_%H%M%S).log"
echo "Starting evaluation for model: $model_to_eval at $(date)" | tee "$log_file"
echo "Log file: $log_file" | tee -a "$log_file"
if [ -n "$START_ID_ARG" ] || [ -n "$END_ID_ARG" ]; then
    echo "Filtering by test_ID range: start=${START_ID_ARG:-min}, end=${END_ID_ARG:-max}" | tee -a "$log_file"
fi


# Evaluation
# Build list of test files (from metadata), optionally filtering by test_ID range
METADATA_FILE="$DAFNYBENCH_ROOT/DafnyBench/metadata/hints_removed_metadata.csv"

# Load all filenames from metadata (column 2), sanitize quotes/CRLF
mapfile -t ALL_METADATA_FILES < <(
  awk -F, 'NR>1 {sub(/\r$/,"",$0); gsub(/^"|"$/,"",$2); print $2}' "$METADATA_FILE"
)

if [ -n "$START_ID_ARG" ] || [ -n "$END_ID_ARG" ]; then
	START_NUM=${START_ID_ARG:-0}
	END_NUM=${END_ID_ARG:-999999}
	mapfile -t SELECTED_TEST_FILES < <(
	  awk -F, -v s="$START_NUM" -v e="$END_NUM" '
	    NR>1 {sub(/\r$/,"",$0); gsub(/^"|"$/,"",$1); gsub(/^"|"$/,"",$2);
	           id=$1+0; if (id>=s && id<=e) print $2}' "$METADATA_FILE"
	)
else
	# All-file case: expect exactly all IDs from metadata (no more)
	SELECTED_TEST_FILES=("${ALL_METADATA_FILES[@]}")
fi

# Materialize to full paths and verify existence
DAFNY_FILES=()
for tf in "${SELECTED_TEST_FILES[@]}"; do
	full="$TEST_SET_DIR/$tf"
	if [ -f "$full" ]; then
		DAFNY_FILES+=("$full")
	fi
done

# Shuffle selection robustly (handles spaces/newlines)
if [ ${#DAFNY_FILES[@]} -gt 0 ]; then
	mapfile -d '' DAFNY_FILES < <(printf '%s\0' "${DAFNY_FILES[@]}" | shuf -z)
fi

echo "Total selected files: ${#DAFNY_FILES[@]} (expected from metadata: ${#SELECTED_TEST_FILES[@]})" | tee -a "$log_file"

# Validate counts; list up to 20 missing; in all-file case also list extras on disk
if [ ${#DAFNY_FILES[@]} -ne ${#SELECTED_TEST_FILES[@]} ]; then
	echo "Mismatch between selected files and metadata expectation." | tee -a "$log_file"
	missing=0
	for tf in "${SELECTED_TEST_FILES[@]}"; do
		full="$TEST_SET_DIR/$tf"
		if [ ! -f "$full" ]; then
			echo "Missing file referenced by metadata: $full" | tee -a "$log_file"
			missing=$((missing+1))
			[ $missing -ge 20 ] && break
		fi
	done
	extras=0
	if [ -z "$START_ID_ARG" ] && [ -z "$END_ID_ARG" ]; then
		# Only in all-file case, report extras on disk not in metadata
		declare -A _meta=()
		for tf in "${SELECTED_TEST_FILES[@]}"; do _meta["$tf"]=1; done
		while IFS= read -r -d '' present; do
			rel="${present#"$TEST_SET_DIR/"}"
			if [ -z "${_meta[$rel]}" ]; then
				echo "Extra file on disk not in metadata: $present" | tee -a "$log_file"
				extras=$((extras+1))
				[ $extras -ge 20 ] && break
			fi
		done < <(find "$TEST_SET_DIR" -maxdepth 1 -type f -name '*.dfy' -print0)
	fi
	echo "Missing count: $missing; Extra count: $extras" | tee -a "$log_file"
	exit 1
fi

# Guard: ensure we actually have files to process
if [ ${#DAFNY_FILES[@]} -eq 0 ]; then
	echo "No .dfy files selected under $TEST_SET_DIR" | tee -a "$log_file"
	exit 1
fi


for DAFNY_FILE in "${DAFNY_FILES[@]}"
do
    echo "Reconstructing $DAFNY_FILE"
    if [ -f "$DAFNY_FILE" ]; then
        FILENAME=$(basename "$DAFNY_FILE")
        # Example Dafny executable path: "/opt/homebrew/bin/Dafny"
        python fill_hints.py \
            --model "$model_to_eval" \
            --test_file "$FILENAME" \
            --feedback_turn 10 \
            --dafny_path "$DAFNY_PATH" \
            --llm_providers "openrouter" \
            --log_file "$log_file"
    fi
done

# Calculate success rate
results_file="../results/results_summary/${model_to_eval}_results.csv"
lines=($(<"$results_file"))
total_num_files=$((${#lines[@]} - 1))
num_failed=0

for ((i=1; i<=total_num_files; i++)); do
    if [[ ${lines[i]} == *"failed" ]]; then
        ((num_failed++))
    fi
done

success_rate=$(echo "scale=2; ($total_num_files - $num_failed) / $total_num_files" | bc)
echo "Success rate for $model_to_eval = $success_rate"
