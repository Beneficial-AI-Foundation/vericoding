import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def ascontiguousarray {n : Nat} (a : Vector Float n) : Id (Vector Float (max n 1)) :=
  sorry

theorem ascontiguousarray_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    ascontiguousarray a
    ⦃⇓result => ⌜
      (max n 1 ≥ 1) ∧
      (n > 0 → max n 1 = n) ∧
      (n = 0 → max n 1 = 1) ∧
      (n > 0 → ∀ i : Fin n, ∃ j : Fin (max n 1), result.get j = a.get i)
    ⌝⦄ := by
  sorry
