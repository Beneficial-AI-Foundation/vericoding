-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermemul {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) : Id (Vector Float (n + m - 1)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermemul_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) 
    (h_n : n > 0) (h_m : m > 0) :
    ⦃⌜n > 0 ∧ m > 0⌝⦄
    hermemul c1 c2
    ⦃⇓result => ⌜(∀ i : Fin n, c1.get i = 0) ∨ (∀ j : Fin m, c2.get j = 0) → 
                   (∀ k : Fin (n + m - 1), result.get k = 0)⌝⦄ := by
  sorry
-- </vc-theorems>