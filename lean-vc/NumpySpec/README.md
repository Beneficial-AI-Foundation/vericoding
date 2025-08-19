# NumpySpec

NumpySpec is a **formally verified numpy-compatible library** for Lean 4, providing mathematically proven implementations of matrix operations with numpy-style APIs.

## Overview

This project aims to port essential numpy functionality to Lean 4 with formal verification, starting with core matrix operations. Unlike traditional numpy implementations, every operation comes with mathematical proofs of correctness.

The core specification is found in `NumpySpec.lean`:

- `Matrix.add`: Element-wise matrix addition with type-safe dimensions
- `Matrix.multiply`: Matrix multiplication with dimension checking  
- `Matrix.transpose`: Matrix transposition preserving mathematical properties
- Future: Broadcasting, linear algebra decompositions, and advanced operations

## Key Features

- **Formal Verification**: Every operation is mathematically proven correct
- **Numpy Compatibility**: Familiar API design for numpy users
- **Type Safety**: Lean's type system prevents dimension mismatches
- **Cloud-Native**: Compilation and verification offloaded to Pantograph servers
- **RL Training**: Reinforcement learning agents for automated theorem proving

## Dependencies

Local machine only needs:

* Python ≥ 3.12 with [`uv`](https://github.com/astral-sh/uv) (see `Justfile`)

## Installation

```bash
git clone https://github.com/Beneficial-AI-Foundation/NumpySpec.git
cd NumpySpec
just sync   # installs all Python deps (Pantograph, LeanTool, …)
```

Everything else (Elan, Lean toolchain) is provisioned automatically in the
remote Pantograph snapshot when you invoke any `just pipeline` target.



## Build

This project uses `just`.

## Cloud Compilation

The project supports remote compilation via Pantograph servers. First run provisions a snapshot (≈ 5 min). Subsequent runs reuse the warmed snapshot/instance.

## Numpy Port Roadmap

### 1. Core Matrix Operations (Current Focus)
- ✅ Basic matrix types with fixed dimensions
- 🚧 Matrix addition, multiplication, transpose
- 📋 Element access and slicing
- 📋 Broadcasting support

### 2. Linear Algebra
- 📋 LU decomposition
- 📋 Matrix inversion
- 📋 Eigenvalue computation
- 📋 SVD decomposition

### 3. Advanced Features
- 📋 Sparse matrix support
- 📋 Batch operations
- 📋 GPU computation integration
- 📋 Performance optimization

### 4. Verification Strategy
- **Spec vs. Exec separation**: Pure mathematical specifications with efficient implementations
- **Refinement proofs**: Each executable function proven correct against its specification
- **Property-based testing**: Integration with Lean's testing framework

## Automated Agent System

NumpySpec includes RL-powered agents for automated development:

### Multi-Agent Architecture

**Core Agents:**
- `LeanEditSubagent`: Applies edits to Lean files with error handling
- `LeanBuildSubagent`: Runs local `lake build` and parses output  
- `LeanRemoteBuildSubagent`: Cloud compilation via Pantograph
- `FeedbackParseSubagent`: Extracts actionable information from build output
- `LakeProjectInitSubagent`: Project initialization and dependency management

**RL Training:**
- PPO-based theorem proving agent
- Custom Lean environment for proof search
- Integration with state-of-the-art language models

### Usage

```python
from numpyspec.rl_env import LeanEnv
from numpyspec.rl_trainer import train_agent

# Train an RL agent for theorem proving
train_agent(steps=10000)

# Use subagents for development automation
from numpyspec.subagents import LeanEditSubagent, LeanBuildSubagent

edit_agent = LeanEditSubagent()
build_agent = LeanBuildSubagent()
```

## Contributing

Contributions welcome! Focus areas:

1. **Core Operations**: Implement matrix operations with formal proofs
2. **API Design**: Ensure numpy compatibility while maintaining mathematical rigor
3. **Performance**: Optimize implementations without sacrificing correctness
4. **Documentation**: Examples showing numpy-to-Lean translation

## Research Applications

NumpySpec enables:
- **Verified Scientific Computing**: Mathematical guarantees for numerical algorithms
- **Educational Tool**: Learn formal methods through familiar numpy operations  
- **AI Safety Research**: Provably correct implementations for safety-critical applications
- **Automated Theorem Proving**: RL agents learning to prove mathematical properties

## License

This project is licensed under the Apache-2.0 license - see the LICENSE file for details.

## Related Projects

- **FuncTracker**: ASCII table parsing for development progress tracking (separate module)
- **NDArray**: NumPy-compatible n-dimensional arrays with formal verification
- **LeanTool**: Integration utilities for Lean development workflows