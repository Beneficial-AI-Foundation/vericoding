import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def fftshift {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry

theorem fftshift_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    fftshift x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x.get ⟨(i.val + n - n / 2) % n, sorry⟩ ∧
                  (∀ j : Fin n, ∃ k : Fin n, result.get k = x.get j) ∧
                  (∀ val : Float, (∃ j : Fin n, x.get j = val) ↔ (∃ k : Fin n, result.get k = val))⌝⦄ := by
  sorry
