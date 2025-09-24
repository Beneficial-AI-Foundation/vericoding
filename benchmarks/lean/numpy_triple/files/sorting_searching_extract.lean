-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def extract {n m : Nat} (condition : Vector Bool n) (arr : Vector Int n) : 
  Id (Vector Int m) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem extract_spec {n m : Nat} (condition : Vector Bool n) (arr : Vector Int n) :
    ⦃⌜True⌝⦄
    extract condition arr
    ⦃⇓result => ⌜-- Each element in result comes from arr at a position where condition is true
      (∀ (k : Fin m), ∃ (i : Fin n), condition.get i = true ∧ result.get k = arr.get i) ∧
      -- The order is preserved: elements appear in the same relative order as in arr
      (∀ (k₁ k₂ : Fin m), k₁ < k₂ → 
        ∃ (i₁ i₂ : Fin n), condition.get i₁ = true ∧ condition.get i₂ = true ∧
        result.get k₁ = arr.get i₁ ∧ result.get k₂ = arr.get i₂ ∧ i₁ < i₂) ∧
      -- Every True position in condition contributes exactly one element to the result  
      (∀ (i : Fin n), condition.get i = true → 
        ∃ (k : Fin m), result.get k = arr.get i)⌝⦄ := by
  sorry
-- </vc-theorems>