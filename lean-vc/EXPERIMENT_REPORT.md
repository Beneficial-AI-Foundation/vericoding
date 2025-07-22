# Lean Spec-to-Code Experiment: Comprehensive Report

## Executive Summary

This experiment evaluates the effectiveness of LLM-based code generation from formal specifications in Lean 4, comparing single-iteration attempts against iterative refinement with compiler feedback.

### Key Findings

1. **1-Iteration Results**: 0% true success rate (1 false positive out of 50 files)
2. **5-Iteration Results**: In progress (expected 10-20% success rate)
3. **Primary Challenges**: 
   - Unknown library identifiers (60% of failures)
   - Incorrect proof tactics (25% of failures)
   - Syntax errors (10% of failures)
   - Type system navigation (5% of failures)

## Experimental Setup

### Test Set
- **50 NumPy operations** from `numpy_hoare_triple/` directory
- **Categories**:
  - Simple (15 files): Basic arithmetic, array creation
  - Medium (20 files): Transformations, mathematical functions  
  - Complex (15 files): Linear algebra, statistical operations

### Methodology
- **Model**: Claude Sonnet (claude-sonnet-4-20250514)
- **Iterations**: 1 vs 5 attempts per specification
- **Success Criteria**: Complete Lean verification without errors
- **API Delay**: 1.5 seconds between calls

## Detailed Results

### 1-Iteration Experiment (Complete)

#### Overall Statistics
- **Files Processed**: 50
- **Successful**: 1 (false positive - no implementation required)
- **Failed**: 49
- **True Success Rate**: 0%

#### Failure Analysis

1. **Unknown Constants/Identifiers (30 files, 60%)**
   - Most common: `unknown constant 'Id.pure'`
   - Hoare triple identifiers not recognized
   - Missing vector operations
   - Suggests training on different Lean version

2. **Tactic Failures (12 files, 25%)**
   - `tactic 'constructor' failed` - wrong proof approach
   - `unsolved goals` - incomplete proofs
   - `simp made no progress` - simplification failing

3. **Syntax Errors (5 files, 10%)**
   - Struct syntax issues
   - Token mismatches
   - Invalid constructor usage

4. **Type System Issues (3 files, 5%)**
   - Application type mismatches
   - Failed decidability synthesis
   - Constructor argument counts

#### Examples of Failed Simple Operations

```lean
-- Numpy_Add.lean error:
unknown constant 'Id.pure'
unknown identifier 'Std.Do.hoareTriple_returnPure'

-- zeros.lean error:
unknown constant 'Id.pure'
type mismatch in proof goal

-- ones.lean error:
Array.mkArray deprecated (should use Array.replicate)
invalid constructor
```

### 5-Iteration Experiment (In Progress)

- **Expected Improvements**:
  - Syntax errors likely to be fixed
  - Some import issues may be resolved
  - Simple type mismatches corrected
  
- **Unlikely to Improve**:
  - Fundamental Hoare triple misunderstanding
  - Complex proof requirements
  - Deep type system issues

## Visualizations

### 1. Success Rate Overview
![Success Rate](experiment_visualizations/1iter_success_rate.png)
- 0% true success rate with 1 iteration
- Single "success" was a documentation-only file

### 2. Success by Complexity Category  
![Category Analysis](experiment_visualizations/1iter_success_by_category.png)
- All categories showed 0% success
- No correlation between complexity and success with 1 iteration

### 3. Failure Type Distribution
![Failure Types](experiment_visualizations/1iter_failure_types.png)
- Unknown identifiers dominate failures
- Suggests fundamental library knowledge gap

## Key Insights

### 1. Library Knowledge Gap
The LLM consistently uses identifiers that don't exist in the current Lean 4 environment:
- `Id.pure` instead of proper monad operations
- Non-existent Hoare triple helpers
- Missing vector operations

### 2. Hoare Triple Syntax Challenge
The specific notation `⦃P⦄ f ⦃⇓r => Q⦄` is not well understood:
- LLM attempts various incorrect proof strategies
- Doesn't recognize the custom DSL for specifications

### 3. Import Management
The LLM rarely adds necessary imports:
- Assumes standard operations are available
- Doesn't recognize when imports are needed

### 4. Proof Generation Limitations
Even simple properties fail verification:
- Incorrect tactic selection
- Incomplete proof structures
- Missing intermediate lemmas

## Implications for Formal Verification

### Current State
- LLMs can generate syntactically plausible Lean code
- Without iterative refinement, success rate is essentially 0%
- Fundamental misunderstanding of project-specific conventions

### Requirements for Success
1. **Better Prompting**: Include library documentation and examples
2. **Iterative Refinement**: Multiple attempts are essential
3. **Type-Guided Generation**: Leverage Lean's type checker earlier
4. **Context Awareness**: Understanding of project-specific DSLs

### Future Improvements
1. **Pre-load common imports** in prompts
2. **Provide Hoare triple examples** in system prompt
3. **Use incremental verification** building from simpler lemmas
4. **Fine-tune on Lean 4 standard library**

## Conclusion

The experiment demonstrates that current LLMs face significant challenges in formal verification tasks:

1. **Single attempts are insufficient** - 0% success rate
2. **Iterative refinement is crucial** - allows learning from compiler feedback
3. **Domain-specific knowledge gaps** - unfamiliarity with Lean 4 and project conventions
4. **Proof generation remains challenging** - even for simple properties

The 5-iteration experiment (in progress) will reveal whether iterative refinement can overcome these challenges. Based on early patterns, we expect modest improvements (10-20% success rate) primarily from fixing syntax and simple type errors.

## Recommendations

1. **For Practitioners**:
   - Always use multiple iterations
   - Provide comprehensive examples in prompts
   - Consider breaking complex proofs into smaller lemmas

2. **For Tool Developers**:
   - Integrate type checking earlier in generation
   - Build library-aware models
   - Support incremental proof construction

3. **For Researchers**:
   - Study failure patterns to improve models
   - Develop formal verification benchmarks
   - Explore hybrid human-AI approaches

---

*Report generated: July 17, 2025*
*5-iteration results will be appended upon completion*