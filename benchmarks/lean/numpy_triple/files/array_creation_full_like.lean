import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_full_like {n : Nat} (a : Vector Float n) (fill_value : Float) : Id (Vector Float n) :=
  sorry

theorem numpy_full_like_spec {n : Nat} (a : Vector Float n) (fill_value : Float) :
    ⦃⌜True⌝⦄
    numpy_full_like a fill_value
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = fill_value⌝⦄ := by
  sorry
