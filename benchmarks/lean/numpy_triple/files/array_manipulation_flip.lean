import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_flip {n : Nat} (m : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem numpy_flip_spec {n : Nat} (m : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_flip m
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = m.get ⟨n - 1 - i.val, by
      have h : i.val < n := i.isLt
      omega⟩⌝⦄ := by
  sorry
