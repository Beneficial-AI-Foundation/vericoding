import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polymulx {n : Nat} (c : Vector Float n) : Id (Vector Float (n + 1)) :=
  sorry

theorem polymulx_spec {n : Nat} (c : Vector Float n) :
    ⦃⌜True⌝⦄
    polymulx c
    ⦃⇓result => ⌜result.get ⟨0, by simp⟩ = 0 ∧ 
                 ∀ i : Fin n, result.get ⟨i.val + 1, by simp⟩ = c.get i⌝⦄ := by
  sorry
