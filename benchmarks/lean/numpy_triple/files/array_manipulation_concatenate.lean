import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def concatenate {n m : Nat} (a : Vector Float n) (b : Vector Float m) : Id (Vector Float (n + m)) :=
  sorry

theorem concatenate_spec {n m : Nat} (a : Vector Float n) (b : Vector Float m) :
    ⦃⌜True⌝⦄
    concatenate a b
    ⦃⇓result => ⌜(∀ i : Fin n, result.get ⟨i.val, by omega⟩ = a.get i) ∧
                 (∀ j : Fin m, result.get ⟨n + j.val, by omega⟩ = b.get j)⌝⦄ := by
  sorry
