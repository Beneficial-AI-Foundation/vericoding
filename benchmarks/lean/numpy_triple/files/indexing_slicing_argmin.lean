-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def argmin {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem argmin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    argmin a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get i ≤ a.get j) ∧ 
           (∀ k : Fin (n + 1), k < i → a.get k > a.get i)⌝⦄ := by
  sorry
-- </vc-theorems>