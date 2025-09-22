-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def upper {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem upper_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    upper a
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Fundamental correctness: result matches Lean's built-in toUpper
      (result = original.toUpper) ∧
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character-level transformation: each character is correctly converted
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          result.get? ⟨j⟩ = some origChar.toUpper) ∧
      -- Idempotent property: applying upper twice gives same result as once
      (result.toUpper = result) ∧
      -- Case preservation: non-alphabetic characters remain unchanged
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (¬origChar.isAlpha → result.get? ⟨j⟩ = some origChar)) ∧
      -- Alphabetic transformation: lowercase letters become uppercase
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (origChar.isLower → result.get? ⟨j⟩ = some origChar.toUpper))⌝⦄ := by
  sorry
-- </vc-theorems>