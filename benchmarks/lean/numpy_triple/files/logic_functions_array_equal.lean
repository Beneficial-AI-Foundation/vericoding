import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def arrayEqual {T : Type} [BEq T] {n : Nat} (a1 a2 : Vector T n) : Id Bool :=
  sorry

theorem arrayEqual_spec {T : Type} [BEq T] {n : Nat} (a1 a2 : Vector T n) :
    ⦃⌜True⌝⦄
    arrayEqual a1 a2
    ⦃⇓result => ⌜(result = true ↔ ∀ i : Fin n, a1.get i == a2.get i) ∧
                  (n = 0 → result = true) ∧
                  (∃ i : Fin n, ¬(a1.get i == a2.get i) → result = false)⌝⦄ := by
  sorry
