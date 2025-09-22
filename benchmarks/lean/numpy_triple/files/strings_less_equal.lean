-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def less_equal {n : Nat} (x1 x2 : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem less_equal_spec {n : Nat} (x1 x2 : Vector String n) :
    ⦃⌜True⌝⦄
    less_equal x1 x2
    ⦃⇓result => ⌜-- Core property: result[i] = (x1[i] <= x2[i]) for all indices
                 (∀ i : Fin n, result.get i = (x1.get i <= x2.get i)) ∧
                 -- Equivalence: result[i] is true iff x1[i] <= x2[i]
                 (∀ i : Fin n, (result.get i = true ↔ x1.get i <= x2.get i)) ∧
                 -- Reflexivity: if inputs are the same, result is all true
                 (x1 = x2 → ∀ i : Fin n, result.get i = true) ∧
                 -- Consistency with string equality: if strings are equal, result is true
                 (∀ i : Fin n, x1.get i = x2.get i → result.get i = true) ∧
                 -- Antisymmetry: if x1[i] <= x2[i] and x2[i] <= x1[i], then x1[i] = x2[i]
                 (∀ i : Fin n, (x1.get i <= x2.get i) ∧ (x2.get i <= x1.get i) → x1.get i = x2.get i) ∧
                 -- Transitivity preservation: consistent with transitive nature of string ordering
                 (∀ i : Fin n, ∀ z : String, x1.get i <= z ∧ z <= x2.get i → x1.get i <= x2.get i) ∧
                 -- Decidability: result is always boolean (true or false)
                 (∀ i : Fin n, result.get i = true ∨ result.get i = false)⌝⦄ := by
  sorry
-- </vc-theorems>