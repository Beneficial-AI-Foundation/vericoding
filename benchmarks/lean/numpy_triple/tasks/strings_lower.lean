-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def lower {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lower_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    lower a
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Fundamental correctness: result matches Lean's built-in toLower
      (result = original.toLower) ∧
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Character-level transformation: each character is correctly converted
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          result.get? ⟨j⟩ = some origChar.toLower) ∧
      -- Idempotent property: applying lower twice gives same result as once
      (result.toLower = result) ∧
      -- Case preservation: non-alphabetic characters remain unchanged
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (¬origChar.isAlpha → result.get? ⟨j⟩ = some origChar)) ∧
      -- Alphabetic transformation: uppercase letters become lowercase
      (∀ j : Nat, j < original.length → 
        ∃ origChar : Char, 
          original.get? ⟨j⟩ = some origChar ∧ 
          (origChar.isUpper → result.get? ⟨j⟩ = some origChar.toLower))⌝⦄ := by
  sorry
-- </vc-theorems>