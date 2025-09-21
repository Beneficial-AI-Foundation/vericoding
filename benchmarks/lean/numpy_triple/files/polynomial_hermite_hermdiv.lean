-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hermdiv {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) (h : m > 0) : 
    Id (Vector Float n × Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hermdiv_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m) (h : m > 0)
    (h_nonzero : ∃ i : Fin m, c2.get i ≠ 0) :
    ⦃⌜m > 0 ∧ ∃ i : Fin m, c2.get i ≠ 0⌝⦄
    hermdiv c1 c2 h
    ⦃⇓result => ⌜let (quo, rem) := result
                -- The remainder has all coefficients zero or its effective degree is less than c2's
                (∀ i : Fin n, rem.get i = 0) ∨ 
                (∃ k : Fin n, (∀ j : Fin n, j ≥ k → rem.get j = 0) ∧
                              (k < m ∨ m > n))⌝⦄ := by
  sorry
-- </vc-theorems>