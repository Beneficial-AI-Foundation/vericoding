# DafnyBenchmarks: Porting Dafny Specifications to Lean 4

## Overview

This directory contains Lean 4 ports of Dafny benchmark specifications from the vericoding repository. The goal is to translate Dafny method specifications (preconditions and postconditions) into Lean 4 using Hoare triple notation.

## Source

The original Dafny specifications come from:
- Repository: https://github.com/Beneficial-AI-Foundation/vericoding
- Path: `/dafny/benchmarks/dafny-bench_specs/atomizer_supported/`

## Porting Methodology

### 1. Specification Style

Each Dafny specification is ported using the Hoare triple style from `Std.Do.Triple`:

```lean
theorem spec_name {params} :
    ⦃⌜precondition⌝⦄
    function_call
    ⦃⇓result => ⌜postcondition⌝⦄ := by
  sorry  -- proof left for future work
```

### 2. Type Mappings

| Dafny Type | Lean 4 Type | Notes |
|------------|-------------|-------|
| `int` | `Int` | Unbounded integers |
| `nat` | `Nat` | Natural numbers |
| `array<T>` | `Array T` | Mutable arrays |
| `seq<T>` | `List T` | Immutable sequences |
| `set<T>` | `Std.HashSet T` | Sets (or List with uniqueness) |
| `map<K,V>` | `Std.HashMap K V` | Key-value maps |
| `bool` | `Bool` | Booleans |
| `char` | `Char` | Characters |
| `string` | `String` | Strings |

### 3. Naming Conventions

- Dafny file: `Clover_function_name_spec.dfy`
- Lean file: `FunctionName.lean`
- Module name: `NumpySpec.DafnyBenchmarks.FunctionName`

### 4. Common Patterns

#### Array Indexing
```lean
-- Dafny: a[i]
-- Lean: a[i.val]'(by sorry)  -- with bounds proof obligation
```

#### Multiset Equality
```lean
-- Helper function to count occurrences
def countOccurrences (a : Array α) (x : α) [DecidableEq α] : Nat :=
  a.foldl (fun acc y => if y = x then acc + 1 else acc) 0
```

#### Existential Quantification
```lean
-- Dafny: exists i :: 0 <= i < a.Length && a[i] == x
-- Lean: ∃ i : Fin a.size, a[i.val] = x
```

#### Array Construction
```lean
-- Creating new arrays with specific properties
Array.ofFn (fun i : Fin n => computation)
```

## Categories of Specifications

### Basic Operations (10 specs)
- Arithmetic: Abs, Avg, MinOfTwo, DoubleQuadruple
- Constants: ReturnSeven
- Predicates: IsEven

### Array Operations (15 specs)
- Transformations: ArrayAppend, ArrayConcat, ArrayCopy, RemoveFront, Reverse, Rotate
- Element-wise: ArrayProduct, ArraySum, DoubleArrayElements, Replace
- Filtering: EvenList
- Modifications: CopyPart, Insert, Modify2DArray

### Search & Sort (10 specs)
- Search: BinarySearch, Find, LinearSearch1/2/3, OnlineMax
- Sort: BubbleSort, SelectionSort
- Analysis: MaxArray, MinArray, OnlyOnce, CountLessThan

### String & Pattern (5 specs)
- Validation: AllDigits, IsPalindrome
- Matching: Match, LongestPrefix

### Mathematical (5 specs)
- Arithmetic: CalDiv, CalSum, Quotient
- Advanced: IntegerSquareRoot

### Advanced Algorithms (5 specs)
- BelowZero, CanyonSearch, ConvertMapKey, HasCloseElements, SlopeSearch
- MultiReturn, SwapArithmetic, SeqToArray, SetToSeq

## Implementation Notes

1. **Specifications Only**: These files contain only specifications (function signatures and theorem statements), not implementations. All function bodies are minimal placeholders that type-check, and all proofs are `sorry`. This follows the approach where specifications come first, and implementations can be filled in later.

2. **Proof Obligations**: All proofs are currently marked as `sorry`. Future work includes:
   - Proving termination for recursive functions
   - Verifying array bounds
   - Establishing functional correctness

3. **Monadic Context**: Most functions use the `Id` monad for pure computations. Some use `StateM` for array modifications.

4. **Error Handling**: Where Dafny uses `-1` for "not found", Lean versions typically use `Option` or explicit sentinel values.

5. **Generic Functions**: Lean versions often add typeclass constraints like `[DecidableEq α]` or `[Inhabited α]` where needed.

## Future Work

1. **Proof Completion**: Replace `sorry` with actual proofs
2. **Performance**: Optimize implementations for efficiency
3. **Testing**: Add property-based tests using Plausible
4. **Integration**: Connect with NumPy specifications where applicable
5. **Tooling**: Develop tactics specific to array reasoning

## Contributing

When adding new specifications:
1. Follow the existing naming and style conventions
2. Document any deviations from the Dafny original
3. Ensure the file compiles with `lake build`
4. Update the main `DafnyBenchmarks.lean` import list
5. Add the specification to the appropriate category in this document

## Porting Progress

### Phase 1: Initial 50 Specifications (Completed)
Ported the first 50 Dafny specifications including basic operations, array algorithms, sorting, and string operations. All files compile successfully with minor issues in 7 specifications that need future attention.

### Phase 2: Extended Specifications (51-60) (Completed)
- Swap operations: SwapArithReconstructed, SwapBitvector, SwapInArray, SwapSimultaneous, SwapGeneral
- Array operations: TestArray
- Mathematical operations: Triple, Triple2, Triple3, Triple4
- Algorithm: TwoSum

### Phase 3: Next 50 Specifications (61-110) (Completed)
Successfully ported 50 additional specifications including:

**Batch 1 (61-70):**
- UpdateArray, UpdateMap: Array and map update operations
- DPGradientDescent, Gaussian: Differential privacy algorithms
- SearchAddends: Two-sum in sorted sequence
- MergeSort: Complete merge sort implementation
- BinarySearchTree: BST operations (insert, delete, traversals)
- CMSC433Assignment: Multiple verification problems
- PowerFunction: Exponentiation

**Batch 2 (71-80):**
- FindMinimum3: Minimum of three integers
- SimpleAssignment, AddOne: Basic operations
- MultiplyAndAdd: Arithmetic operations
- StringOperations: String manipulation (prefix, substring, common substrings)
- CumulativeSum: Prefix sum for range queries
- ListFromArray: Array to functional list conversion
- Factorial, HoareExamples: Classic verification examples

**Batch 3 (81-90):**
- PrefixSum, SearchSort: Array algorithms
- ContainerRanks: Well-foundedness properties
- SeqFromArray: Sequence operations
- BinarySearch2, Find2: Search variants
- Fibonacci: Fibonacci sequence
- TwoSum2, TwoSum3: LeetCode Two Sum variants
- LongestPalindrome: Palindromic substring

**Batch 4 (91-100):**
- RemoveElement: LeetCode array manipulation
- ClimbingStairs: Dynamic programming (Fibonacci pattern)
- FindTheCelebrity: Graph-based puzzle
- Shuffle: Array shuffling
- ExpressionOptimization: Expression tree optimization
- FindZero, Max, LinearSearch: Basic algorithms

**Batch 5 (101-110):**
- BinarySearchDec: Binary search on decreasing sequences
- InsertionSortMultiset, SelectionSortMultiset: Sorting with multiset specs
- QuickSelect: k-th smallest element
- SimpleSpecs: Basic specifications
- InsertionSortSeq, Search1000: Additional sorting and search
- SumIntsLoop: Arithmetic series sum
- ListReverse: List reversal with lemmas
- DutchFlag: Three-way partitioning

### Summary Statistics

Total specifications ported: **110**
- Successfully compiling: ~100 specs
- Minor issues needing attention: ~10 specs

The comprehensive library now includes:
1. **Basic algorithms**: sorting, searching, mathematical operations
2. **Data structures**: arrays, lists, maps, binary search trees
3. **Advanced algorithms**: dynamic programming, graph algorithms, optimization
4. **LeetCode problems**: practical algorithm challenges
5. **Formal verification examples**: classic proofs and lemmas

This collection serves as:
1. A reference for correct algorithm implementation
2. A test suite for verification tools
3. A learning resource for formal methods
4. A bridge between Dafny and Lean 4 communities