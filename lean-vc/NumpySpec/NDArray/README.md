# NDArray

A numpy-compatible n-dimensional array implementation in Lean 4.

## Overview

NDArray provides:
- N-dimensional arrays with static shape information
- Row-major memory layout (compatible with NumPy)
- Type-safe indexing with compile-time bounds checking
- Support for basic arithmetic operations
- Memory-efficient storage using Lean's ByteArray

## Usage

```lean
import NDArray

-- Create a 2x3 array
let shape : Vector Nat 2 := ⟨[2, 3], rfl⟩
let arr := NDArray.fromList shape [1.0, 2.0, 3.0, 4.0, 5.0, 6.0]

-- Access elements with compile-time safe indexing
let idx : Index shape := Index.fromArray? shape [1, 2]
let value := arr[idx]  -- Returns 6.0
```

## Design

NDArray follows NumPy's design principles:
- Contiguous memory storage for cache efficiency
- Row-major (C-style) ordering
- Strided indexing for views and slices
- Type safety through Lean's dependent types