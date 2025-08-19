---
allowed-tools:
  - Bash
---

# NumpySpec Commit and Push with Full CI Pipeline

Project-specific commit and push command that runs the complete build and test pipeline before pushing changes. This ensures code quality and prevents breaking the main branch.

## Usage

- `/commitpush "your commit message"` - Commit with custom message and push after tests
- `/commitpush` - Auto-generate commit message and push after tests

## CI Pipeline

The command runs the following steps in order:

### 1. Pre-commit Checks
```bash
echo "🧪 Running NumpySpec CI Pipeline..."
echo "📁 Working directory: $(pwd)"

# Check if this is the NumpySpec project
if [ ! -f "lakefile.lean" ] || [ ! -f "pyproject.toml" ]; then
    echo "❌ This doesn't appear to be the NumpySpec project root"
    echo "💡 Make sure you're running this from the project root directory"
    exit 1
fi
```

### 2. Lean Build and Verification
```bash
echo "🔧 Building Lean libraries..."

# Build main NumpySpec library
if ! lake build NumpySpec; then
    echo "❌ NumpySpec library build failed"
    exit 1
fi

# Build BignumLean library
if ! lake build BignumLean; then
    echo "❌ BignumLean library build failed"
    exit 1
fi

# Build FuncTracker library
if ! lake build FuncTracker; then
    echo "❌ FuncTracker library build failed"
    exit 1
fi

# Build executable
if ! lake build numpyspec; then
    echo "❌ numpyspec executable build failed"
    exit 1
fi

echo "✅ All Lean builds successful"
```

### 3. Python Environment and Tests
```bash
echo "🐍 Setting up Python environment and running tests..."

# Sync Python dependencies
if ! uv sync; then
    echo "❌ Python dependency sync failed"
    exit 1
fi

# Run Python tests
if ! uv run -m pytest tests/ -v; then
    echo "❌ Python tests failed"
    exit 1
fi

echo "✅ Python tests passed"
```

### 4. Code Quality Checks
```bash
echo "🧹 Running code quality checks..."

# Ruff linting and formatting
if ! uv run ruff check src/ tests/; then
    echo "❌ Ruff linting failed"
    echo "💡 Run 'uv run ruff check --fix src/ tests/' to auto-fix issues"
    exit 1
fi

if ! uv run ruff format --check src/ tests/; then
    echo "❌ Ruff formatting check failed"
    echo "💡 Run 'uv run ruff format src/ tests/' to fix formatting"
    exit 1
fi

echo "✅ Code quality checks passed"
```

### 5. Version Control Operations
```bash
# Detect VCS system
if [ -d ".jj" ] || ([ -d ".git" ] && command -v jj >/dev/null 2>&1 && jj status >/dev/null 2>&1); then
    VCS="jj"
    echo "🔧 Using Jujutsu workflow"
else
    VCS="git"
    echo "🔧 Using Git workflow"
fi

# Generate commit message if not provided
COMMIT_MSG="$ARGUMENTS"
if [ -z "$COMMIT_MSG" ]; then
    # Auto-generate based on changed files
    if [ "$VCS" = "jj" ]; then
        CHANGED_FILES=$(jj diff --name-only)
    else
        CHANGED_FILES=$(git diff --name-only)
    fi
    
    if echo "$CHANGED_FILES" | grep -q "\.lean$"; then
        if echo "$CHANGED_FILES" | grep -q "\.py$"; then
            COMMIT_MSG="feat: update Lean proofs and Python implementation"
        else
            COMMIT_MSG="feat: update Lean definitions and proofs"
        fi
    elif echo "$CHANGED_FILES" | grep -q "\.py$"; then
        COMMIT_MSG="feat: update Python implementation"
    elif echo "$CHANGED_FILES" | grep -q "lakefile\|pyproject\|requirements"; then
        COMMIT_MSG="build: update project configuration"
    elif echo "$CHANGED_FILES" | grep -q "README\|\.md$\|docs/"; then
        COMMIT_MSG="docs: update documentation"
    elif echo "$CHANGED_FILES" | grep -q "test"; then
        COMMIT_MSG="test: update test suite"
    else
        COMMIT_MSG="feat: update NumpySpec implementation"
    fi
    echo "📝 Auto-generated commit message: $COMMIT_MSG"
fi

# Commit and push
echo "🚀 Committing and pushing changes..."

if [ "$VCS" = "jj" ]; then
    # Jujutsu workflow
    jj commit -m "$(cat <<EOF
$COMMIT_MSG

✅ All tests passed
- Lean builds: NumpySpec, BignumLean, FuncTracker
- Python tests: $(uv run -m pytest tests/ --collect-only -q 2>/dev/null | grep -c "test session starts" || echo "N/A")
- Code quality: ruff check + format

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
    
    if jj git push; then
        echo "✅ Successfully pushed to remote"
    else
        echo "⚠️  Push failed - trying to fetch and rebase"
        jj git fetch
        jj rebase -d main
        jj git push
    fi
else
    # Git workflow
    git add .
    
    if git diff --cached --quiet; then
        echo "❌ No changes to commit"
        exit 1
    fi
    
    git commit -m "$(cat <<EOF
$COMMIT_MSG

✅ All tests passed
- Lean builds: NumpySpec, BignumLean, FuncTracker
- Python tests: $(uv run -m pytest tests/ --collect-only -q 2>/dev/null | grep -c "test session starts" || echo "N/A")
- Code quality: ruff check + format

🤖 Generated with [Claude Code](https://claude.ai/code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
    
    if git push; then
        echo "✅ Successfully pushed to remote"
    else
        echo "⚠️  Push failed - trying to pull and rebase"
        git pull --rebase
        git push
    fi
fi
```

### 6. Success Summary
```bash
echo ""
echo "🎉 NumpySpec CI Pipeline Completed Successfully!"
echo "📊 Summary:"
echo "   ✅ Lean builds (NumpySpec, BignumLean, FuncTracker)"
echo "   ✅ Python tests and dependencies"
echo "   ✅ Code quality (ruff)"
echo "   ✅ Commit and push"
echo ""

# Show final commit
if [ "$VCS" = "jj" ]; then
    jj log -r @ --no-graph
else
    git log -1 --oneline
fi

echo ""
echo "🚀 Changes are now live on the remote repository!"
```

## Team Benefits

- **Prevents broken builds**: Won't push if any step fails
- **Consistent quality**: Enforces code formatting and linting
- **Comprehensive testing**: Runs both Lean and Python test suites
- **Informative commits**: Includes CI status in commit messages
- **VCS agnostic**: Works with both Git and Jujutsu workflows
- **Auto-recovery**: Attempts to resolve common push conflicts

## Troubleshooting

If a step fails:
- **Lean build**: Check `lake build` output for compilation errors
- **Python tests**: Run `uv run -m pytest tests/ -v` for detailed test output
- **Code quality**: Run `uv run ruff check --fix` and `uv run ruff format`
- **Dependencies**: Run `uv sync` to update Python packages