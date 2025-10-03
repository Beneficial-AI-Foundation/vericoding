#!/bin/bash
# Smoke test for vericoder.py across all languages
# Usage: ./scripts/test_vericoder_smoke.sh [language]
#   language: lean, verus, dafny, or 'all' (default: all)

set -e  # Exit on error

LANGUAGE="${1:-all}"
LLM="${2:-claude-sonnet}"
ITERATIONS="${3:-1}"
LIMIT="${4:-1}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "🧪 Vericoder Smoke Tests"
echo "========================"
echo "Language: $LANGUAGE"
echo "LLM: $LLM"
echo "Iterations: $ITERATIONS"
echo "Files per language: $LIMIT"
echo ""

# Check for API key
if [ -z "$OPENROUTER_API_KEY" ] && [ -z "$ANTHROPIC_API_KEY" ] && [ -z "$OPENAI_API_KEY" ]; then
    echo -e "${YELLOW}⚠️  Warning: No API key found. Set OPENROUTER_API_KEY, ANTHROPIC_API_KEY, or OPENAI_API_KEY${NC}"
    echo "Tests will validate structure only (no LLM calls)"
    echo ""
fi

test_lean() {
    echo -e "${YELLOW}Testing Lean...${NC}"
    if [ -d "benchmarks/lean/test" ]; then
        uv run src/vericoder.py lean benchmarks/lean/test \
            --llm "$LLM" \
            --limit "$LIMIT" \
            --iterations "$ITERATIONS" \
            --no-wandb \
            --workers 1
        echo -e "${GREEN}✓ Lean test passed${NC}"
    else
        echo -e "${RED}✗ Lean test directory not found${NC}"
        return 1
    fi
}

test_verus() {
    echo -e "${YELLOW}Testing Verus...${NC}"
    # Find first available test directory
    TEST_DIR=$(find benchmarks/verus -type d \( -name "files" -o -name "test" \) 2>/dev/null | head -1)
    if [ -n "$TEST_DIR" ]; then
        echo "Using test directory: $TEST_DIR"
        uv run src/vericoder.py verus "$TEST_DIR" \
            --llm "$LLM" \
            --limit "$LIMIT" \
            --iterations "$ITERATIONS" \
            --no-wandb \
            --workers 1
        echo -e "${GREEN}✓ Verus test passed${NC}"
    else
        echo -e "${RED}✗ Verus test directory not found${NC}"
        return 1
    fi
}

test_dafny() {
    echo -e "${YELLOW}Testing Dafny...${NC}"
    # Find first available test directory
    TEST_DIR=$(find benchmarks/dafny -type d \( -name "files" -o -name "test" \) 2>/dev/null | head -1)
    if [ -n "$TEST_DIR" ]; then
        echo "Using test directory: $TEST_DIR"
        uv run src/vericoder.py dafny "$TEST_DIR" \
            --llm "$LLM" \
            --limit "$LIMIT" \
            --iterations "$ITERATIONS" \
            --no-wandb \
            --workers 1
        echo -e "${GREEN}✓ Dafny test passed${NC}"
    else
        echo -e "${RED}✗ Dafny test directory not found${NC}"
        return 1
    fi
}

test_config() {
    echo -e "${YELLOW}Testing configuration loading...${NC}"
    uv run python -c "
from src.vericoding.core.config import ProcessingConfig
from src.vericoding.core.prompts import PromptLoader

languages = ProcessingConfig.get_available_languages()
print(f'✓ Found {len(languages)} language configurations')

for lang_name, lang_config in languages.items():
    print(f'  - {lang_config.name}')
    prompt_loader = PromptLoader(lang_name, prompts_file=lang_config.prompts_file)
    validation = prompt_loader.validate_prompts()
    if not validation.valid:
        print(f'    ✗ Missing prompts: {validation.missing}')
        exit(1)
    print(f'    ✓ {len(validation.available)} prompts loaded')

print('✓ All configurations valid')
"
    echo -e "${GREEN}✓ Configuration test passed${NC}"
}

# Run tests based on language selection
failed_tests=()

if [ "$LANGUAGE" = "all" ]; then
    # Test configuration first
    test_config || failed_tests+=("config")
    echo ""
    
    # Test each language
    test_lean || failed_tests+=("lean")
    echo ""
    
    test_verus || failed_tests+=("verus")
    echo ""
    
    test_dafny || failed_tests+=("dafny")
    echo ""
else
    case "$LANGUAGE" in
        lean)
            test_lean || failed_tests+=("lean")
            ;;
        verus)
            test_verus || failed_tests+=("verus")
            ;;
        dafny)
            test_dafny || failed_tests+=("dafny")
            ;;
        config)
            test_config || failed_tests+=("config")
            ;;
        *)
            echo -e "${RED}Unknown language: $LANGUAGE${NC}"
            echo "Use: lean, verus, dafny, config, or all"
            exit 1
            ;;
    esac
fi

# Print summary
echo "========================"
if [ ${#failed_tests[@]} -eq 0 ]; then
    echo -e "${GREEN}✅ All tests passed!${NC}"
    exit 0
else
    echo -e "${RED}❌ Failed tests: ${failed_tests[*]}${NC}"
    exit 1
fi

