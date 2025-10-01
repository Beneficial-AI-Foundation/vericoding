#!/bin/bash

# Usage helper
print_usage() {
    echo "Usage: $0 [--start-id N] [--end-id M] <model1> [model2 ... modelN]"
    echo "Examples:"
    echo "  $0 --start-id 0 --end-id 99 gemini-2.5-pro gpt-5-mini"
    echo "  $0 gpt-5-mini"
    echo ""
    echo "Available models include:"
    echo "  - gemini-2.5-pro, gemini-2.5-flash"
    echo "  - grok-4, grok-code-fast-1"
    echo "  - gpt-5-mini, gpt-5"
    echo "  - glm-4.5"
    echo "  - deepseek-chat-v3.1"
    echo "  - claude-sonnet-4, claude-opus-4.1"
}

# Parse flags and positional model names
START_ID=""
END_ID=""
MODELS=()

while [ $# -gt 0 ]; do
    case "$1" in
        --start-id)
            START_ID="$2"; shift 2 ;;
        --start-id=*)
            START_ID="${1#*=}"; shift ;;
        --end-id)
            END_ID="$2"; shift 2 ;;
        --end-id=*)
            END_ID="${1#*=}"; shift ;;
        -h|--help)
            print_usage; exit 0 ;;
        --)
            shift; break ;;
        -*)
            echo "Unknown option: $1"; print_usage; exit 1 ;;
        *)
            MODELS+=("$1"); shift ;;
    esac
done

# Append any remaining args as models
for arg in "$@"; do
    MODELS+=("$arg")
done

if [ ${#MODELS[@]} -eq 0 ]; then
    print_usage
    exit 1
fi

export DAFNYBENCH_ROOT=/home/ubuntu/dafnybench_openrouter

# set DAFNY_PATH and API keys in .env file
# Load environment variables from .env file
if [ -f "$DAFNYBENCH_ROOT/.env" ]; then
    source $DAFNYBENCH_ROOT/.env
fi

export LOG_DIR=$DAFNYBENCH_ROOT/results/logs


# Export range for downstream script
export START_ID
export END_ID

# Loop through all provided model names
for model in "${MODELS[@]}"; do
    echo "Running evaluation for model: $model"
    export model_to_eval="$model"
    # Pass through range flags if provided
    bash ./run_eval_openrouter.sh ${START_ID:+--start-id "$START_ID"} ${END_ID:+--end-id "$END_ID"}
    echo "Completed evaluation for model: $model"
    echo ""
done

echo "All model evaluations completed!"