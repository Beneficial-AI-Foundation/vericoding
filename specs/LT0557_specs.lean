-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_argmin {n : Nat} (a : Vector Float (n + 1)) : Id (Fin (n + 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_argmin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_argmin a
    ⦃⇓i => ⌜(∀ j : Fin (n + 1), a.get i ≤ a.get j) ∧ 
             (∀ j : Fin (n + 1), a.get j = a.get i → i ≤ j)⌝⦄ := by
  sorry
-- </vc-theorems>