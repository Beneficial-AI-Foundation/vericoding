import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def amin {n : Nat} (a : Vector Float (n + 1)) : Id Float :=
  sorry

theorem amin_spec {n : Nat} (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    amin a
    ⦃⇓result => ⌜(∃ i : Fin (n + 1), a.get i = result) ∧
                (∀ i : Fin (n + 1), result ≤ a.get i)⌝⦄ := by
  sorry
