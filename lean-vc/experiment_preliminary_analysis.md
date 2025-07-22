# Lean Spec-to-Code Experiment: Preliminary Analysis

## Experiment Setup

### Objective
Evaluate the effectiveness of LLM-based code generation from formal specifications in Lean 4, testing how iteration count affects success rates.

### Methodology
- **Test Set**: 50 cherry-picked NumPy operations from `numpy_hoare_triple/`
- **Categories**: 
  - Simple (15 files): Basic arithmetic, array creation
  - Medium (20 files): Transformations, mathematical functions
  - Complex (15 files): Linear algebra, statistical operations
- **Iterations**: 1 vs 5 attempts per specification
- **Model**: Claude Sonnet (claude-sonnet-4-20250514)

### Selected Specifications
The 50 specifications were chosen to represent a diverse range of:
1. **Computational complexity**: From O(1) operations to O(n²) algorithms
2. **Type complexity**: Simple vectors to multi-dimensional arrays
3. **Mathematical properties**: Commutativity, associativity, numerical stability
4. **Lean features**: Type classes, dependent types, proof obligations

## Early Observations (First 14 Files)

### Success Patterns
From initial results, successful implementations tend to have:
- Simple, direct mathematical operations
- Clear type signatures without complex dependencies
- Minimal proof obligations in the specification

### Failure Patterns
Common failure modes observed:
1. **Type System Issues**:
   - Incorrect constructor arguments (e.g., `Vector.mk` expects 2 args, only 1 provided)
   - Unknown constants/identifiers (e.g., `Vector.get_zipWith`)
   - Type mismatches in proof goals

2. **Syntax Errors**:
   - Unexpected tokens (often `:` where `}` expected)
   - Incorrect struct field syntax
   - Missing imports or dependencies

3. **Proof Failures**:
   - Unsolved goals with `sorry` placeholders
   - Incorrect proof tactics
   - Missing lemmas for basic properties

### Example Failure Analysis

#### Numpy_Multiply.lean (1 iteration):
```
error: invalid constructor ⟨...⟩, insufficient number of arguments
error: unknown constant 'Vector.get_zipWith'
error: unsolved goals
```
The LLM attempted to use a zipWith pattern but failed to:
1. Import necessary libraries
2. Use correct constructor syntax
3. Provide proper proof of correctness

## Expected Results

### Hypothesis
Based on early observations:
- **1 iteration**: 10-20% success rate (mostly simple operations)
- **5 iterations**: 30-50% success rate (iterative refinement helps)
- **Complexity correlation**: Simple > Medium > Complex success rates

### Key Factors Affecting Success
1. **Specification clarity**: Well-defined pre/post conditions
2. **Type complexity**: Simpler types = higher success
3. **Proof complexity**: Direct calculations vs. complex reasoning
4. **Library knowledge**: LLM's familiarity with Lean 4 stdlib

## Implications for Formal Verification

### Strengths
- LLMs can generate syntactically plausible Lean code
- Basic mathematical operations are well-understood
- Iterative refinement shows promise

### Limitations
- Type system navigation remains challenging
- Proof generation requires deep mathematical understanding
- Library/import management is error-prone
- Context window limits complex specifications

### Future Improvements
1. **Better prompting**: Include more Lean-specific examples
2. **Type-guided generation**: Leverage Lean's type checker earlier
3. **Incremental verification**: Build up from simpler lemmas
4. **Library awareness**: Pre-load common imports and patterns

## Next Steps
1. Complete both experiments (1-iter and 5-iter)
2. Analyze full results with statistical significance
3. Categorize failure modes systematically
4. Generate visualizations showing success rates by category
5. Draw conclusions about LLM capabilities in formal verification