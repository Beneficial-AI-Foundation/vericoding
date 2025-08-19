import Std.Do.Triple
import Std.Tactic.Do

set_option linter.missingDocs false

/-!
{
  "name": "nout",
  "description": "The number of output arguments",
  "examples": {
    "add.nout": "1",
    "modf.nout": "2",
    "divmod.nout": "2"
  }
}
-/

open Std.Do

/-- Represents a universal function (ufunc) type that captures basic metadata about 
    the number of inputs and outputs. In NumPy, this would be the ufunc object itself. -/
structure UFunc where
  /-- Number of input arguments the ufunc accepts -/
  nin : Nat      
  /-- Number of output arguments the ufunc produces -/
  nout_val : Nat 
  /-- Proof that nout_val is always at least 1, since all ufuncs can take output arguments -/
  h_nout_pos : nout_val ≥ 1

/-- Returns the number of output arguments for a given ufunc.
    This corresponds to the nout attribute of NumPy ufuncs. -/
def nout (ufunc : UFunc) : Id Nat :=
  pure ufunc.nout_val

-- LLM HELPER
lemma triple_pure_of_pure {α : Type*} (f : α) (P : α → Prop) (h : P f) :
    ⦃⌜True⌝⦄ 
    pure f
    ⦃⇓result => ⌜P result⌝⦄ := by
  rw [triple_pure]
  intro _ _
  exact h

/-- Specification: nout returns the number of output arguments of the ufunc.
    
    This specification captures the essential mathematical properties of the nout attribute:
    
    1. **Correctness**: The function returns exactly the nout_val field from the ufunc structure
    2. **Lower bound**: The result is always ≥ 1, since all ufuncs can produce at least one output
    3. **Type safety**: The result is a natural number representing a count
    4. **Determinism**: Given the same ufunc, nout always returns the same value
    
    Mathematical properties:
    - ∀ ufunc : UFunc, nout(ufunc) = ufunc.nout_val  
    - ∀ ufunc : UFunc, nout(ufunc) ≥ 1
    - nout is a pure function (no side effects)
    
    Examples from NumPy documentation:
    - add.nout = 1 (binary operation with single output)
    - modf.nout = 2 (returns fractional and integral parts)
    - divmod.nout = 2 (returns quotient and remainder) -/
theorem nout_spec (ufunc : UFunc) :
    ⦃⌜True⌝⦄
    nout ufunc
    ⦃⇓result => ⌜result = ufunc.nout_val ∧ result ≥ 1⌝⦄ := by
  apply triple_pure_of_pure
  constructor
  · rfl
  · exact ufunc.h_nout_pos