-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def legdiv {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m)
    : Id (Vector Float (max 1 (n - m + 1)) × Vector Float (max 1 (m - 1))) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem legdiv_spec {n m : Nat} (c1 : Vector Float n) (c2 : Vector Float m)
    (h_n : n ≥ 1) (h_m : m ≥ 1) (h_nonzero : ∃ i : Fin m, c2.get i ≠ 0) :
    ⦃⌜n ≥ 1 ∧ m ≥ 1 ∧ ∃ i : Fin m, c2.get i ≠ 0⌝⦄
    legdiv c1 c2
    ⦃⇓result => ⌜
      let quo := result.1
      let rem := result.2
      -- Quotient has correct size
      (quo.size = max 1 (n - m + 1)) ∧
      -- Remainder has correct size
      (rem.size = max 1 (m - 1)) ∧
      -- Division property: when dividend degree < divisor degree, quotient is zero
      (n < m → quo.size = 1 ∧ ∃ h : 0 < quo.size, quo.get ⟨0, h⟩ = 0) ∧
      -- Remainder size constraint
      (rem.size ≤ m)
    ⌝⦄ := by
  sorry
-- </vc-theorems>