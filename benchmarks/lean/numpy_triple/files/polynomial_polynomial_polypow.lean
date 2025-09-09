import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def polypow {n : Nat} (c : Vector Float n) (pow : Nat) : Id (Vector Float (n * pow + 1)) :=
  sorry

theorem polypow_spec {n : Nat} (c : Vector Float (n + 1)) (pow : Nat) :
    ⦃⌜True⌝⦄
    polypow c pow
    ⦃⇓result => ⌜(pow = 0 → result.get ⟨0, by omega⟩ = 1) ∧
                 (pow = 1 → ∀ i : Fin (n + 1), result.get ⟨i.val, by sorry⟩ = c.get i)⌝⦄ := by
  sorry
