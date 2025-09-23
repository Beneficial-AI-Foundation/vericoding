-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def greater {n : Nat} (x1 x2 : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem greater_spec {n : Nat} (x1 x2 : Vector String n) :
    ⦃⌜True⌝⦄
    greater x1 x2
    ⦃⇓result => ⌜-- Core property: result[i] = (x1[i] > x2[i]) for all indices
                 (∀ i : Fin n, result.get i = (x1.get i > x2.get i)) ∧
                 -- Asymmetry: if x1[i] > x2[i], then NOT (x2[i] > x1[i])
                 (∀ i : Fin n, result.get i = true → ¬(x2.get i > x1.get i)) ∧
                 -- Irreflexivity: no string is greater than itself
                 (∀ i : Fin n, x1.get i = x2.get i → result.get i = false) ∧
                 -- Transitivity property (partial): if x1[i] > x2[i] and we have x3, then x1[i] > x3[i] when x3[i] < x2[i]
                 (∀ i : Fin n, result.get i = true → ∀ s : String, s < x2.get i → x1.get i > s) ∧
                 -- Decidability: result is always boolean (true or false)
                 (∀ i : Fin n, result.get i = true ∨ result.get i = false)⌝⦄ := by
  sorry
-- </vc-theorems>