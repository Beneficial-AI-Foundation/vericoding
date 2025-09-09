import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def array_equiv {n : Nat} (a1 a2 : Vector Float n) : Id Bool :=
  sorry

theorem array_equiv_spec {n : Nat} (a1 a2 : Vector Float n) :
    ⦃⌜True⌝⦄
    array_equiv a1 a2
    ⦃⇓result => ⌜result = (∀ i : Fin n, a1.get i = a2.get i)⌝⦄ := by
  sorry
