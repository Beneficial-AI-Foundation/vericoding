-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ldexp {n : Nat} (x1 : Vector Float n) (x2 : Vector Int n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ldexp_spec {n : Nat} (x1 : Vector Float n) (x2 : Vector Int n) :
    ⦃⌜True⌝⦄
    ldexp x1 x2
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = x1.get i * (2 : Float) ^ (Float.ofInt (x2.get i))⌝⦄ := by
  sorry
-- </vc-theorems>