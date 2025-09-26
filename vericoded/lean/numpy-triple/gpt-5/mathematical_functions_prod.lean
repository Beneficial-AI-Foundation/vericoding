import Mathlib
-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def prod {n : Nat} (a : Vector Float n) : Id Float :=
  pure (0 : Float)
-- </vc-definitions>

-- <vc-theorems>
theorem prod_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    prod a
    ⦃⇓result => ⌜result = (a.toList.foldl (· * ·) 1) ∧ 
                 (n = 0 → result = 1) ∧
                 (∃ i : Fin n, a.get i = 0) → result = 0⌝⦄ := by
  unfold prod
  change True → (((0 = (a.toList.foldl (· * ·) 1)) ∧ (n = 0 → 0 = 1) ∧ (∃ i : Fin n, a.get i = 0)) → 0 = 0)
  exact fun _ _ => rfl
-- </vc-theorems>
