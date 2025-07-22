# Lean Code Generation Experiments Summary

## Task: Automated Code Generation from Formal Specifications

### Overview
Experiments were conducted to test the effectiveness of automated code generation from Lean 4 formal specifications using Claude Sonnet. The system takes Lean files with `sorry` placeholders and attempts to generate correct implementations using iterative refinement with compiler feedback.

### Experiment Setup
- **Model**: Claude Sonnet 4 (claude-sonnet-4-20250514)
- **Language**: Lean 4
- **Method**: Iterative refinement using compiler error feedback
- **Verification**: Lean 4 compiler (`lake build`)

### Experiments Conducted

#### 1. Hoare Triple Experiments (51 files)
- **Specification Type**: Hoare triple notation `⦃P⦄ f ⦃⇓r => Q⦄`
- **Files**: NumPy operations with pre/post conditions
- **Results**:
  - 1-iteration: 1/51 success (2.0%)
  - 5-iteration: 6/51 success (11.8%)
  - Successful files: Numpy_Stack, identity, Numpy_Std, Numpy_Prod, Numpy_Absolute, copy

#### 2. Non-Hoare Triple Experiments (Attempted)
- **Specification Type**: Simple theorem-based specifications (sep_thm format)
- **Files**: 49 available non-Hoare files from benchmarks/numpy_specs/sep_thm/
- **Status**: Experiments timed out due to API rate limits and processing time
- **Smaller test**: 10-file experiment also timed out

### Key Findings

1. **Iterative Refinement Works**: Success rate improved from 2% to 11.8% with 5 iterations
2. **Early Success Pattern**:
   - 1 file succeeded on first attempt
   - 3 files succeeded within 3 iterations  
   - 2 files required 4-5 iterations
3. **Complexity Matters**:
   - Simple operations (Stack, Copy, Identity) often succeed
   - Mathematical operations (Absolute, Prod, Std) require moderate iterations
   - Complex operations generally fail even with multiple iterations

### Technical Challenges

1. **Hoare Triple Complexity**: The notation and proof obligations are challenging for automated systems
2. **Type System**: Lean 4's dependent type system requires precise understanding
3. **API Performance**: Each iteration takes 5-10 seconds, making large experiments time-consuming
4. **Timeout Issues**: Non-Hoare experiments couldn't complete due to processing time

### Implementation Details

- **spec_to_code_lean.py**: Main script that orchestrates code generation
- **Inline Dependencies**: Uses PEP 723 syntax for dependency management
- **Error Handling**: Captures compiler errors and feeds them back to Claude
- **CSV Output**: Results saved with links to specifications and implementations

### Recommendations

1. **Increase Iteration Limit**: 10-15 iterations may yield better results
2. **Batch Processing**: Process files in smaller batches to avoid timeouts
3. **Enhanced Prompting**: Include more Lean-specific examples in prompts
4. **Caching**: Cache successful tactics and patterns for reuse
5. **Parallel Processing**: Run multiple files concurrently to reduce total time

### Future Work

1. Complete non-Hoare triple experiments with improved timeout handling
2. Analyze error patterns to identify common failure modes
3. Test with more sophisticated models (e.g., o3-pro)
4. Implement incremental solving strategies
5. Create specialized prompts for different specification types

### Files Generated

- **Results**: benchmarks_generated/experiment_{1,5}iter/results.csv
- **Implementations**: benchmarks_generated/experiment_{1,5}iter/*_impl.lean
- **Analysis Scripts**: create_experiment_report.py, run_non_hoare_experiments_proper.py

This experiment demonstrates the potential for AI-assisted formal verification, while highlighting the significant challenges in automating complex mathematical proofs.