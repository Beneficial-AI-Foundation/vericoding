#!/bin/bash
# Coverage generation script
set -e

echo "🧪 Running tests with coverage..."

# Check if uv is available, otherwise use python -m pytest
if command -v uv &> /dev/null; then
    PYTEST_CMD="uv run pytest"
else
    PYTEST_CMD="python3 -m pytest"
fi

echo "Using: $PYTEST_CMD"

# Run tests with coverage
$PYTEST_CMD tests/ -v \
    --cov=vericoding \
    --cov-report=html \
    --cov-report=xml \
    --cov-report=term-missing

echo ""
echo "📊 Coverage reports generated:"
echo "   - Terminal: (shown above)"
echo "   - HTML: htmlcov/index.html"
echo "   - XML: coverage.xml"

# Check if HTML report was generated and show path
if [[ -f "htmlcov/index.html" ]]; then
    echo ""
    echo "🌐 Open HTML coverage report:"
    echo "   file://$(pwd)/htmlcov/index.html"
fi

echo ""
echo "✅ Coverage analysis complete!"
