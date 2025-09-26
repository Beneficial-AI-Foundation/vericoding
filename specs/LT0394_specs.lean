-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebpts2 (n : Nat) (h : n ≥ 2) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebpts2_spec (n : Nat) (h : n ≥ 2) :
    ⦃⌜n ≥ 2⌝⦄
    chebpts2 n h
    ⦃⇓pts => ⌜-- Points are sorted in ascending order
              (∀ i j : Fin n, i < j → pts.get i ≤ pts.get j) ∧
              -- First point is -1 (cos(π))
              pts.get ⟨0, Nat.zero_lt_of_lt h⟩ = -1 ∧
              -- Last point is 1 (cos(0))
              pts.get ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt h) Nat.zero_lt_one⟩ = 1 ∧
              -- All points are in the range [-1, 1]
              (∀ i : Fin n, -1 ≤ pts.get i ∧ pts.get i ≤ 1) ∧
              -- Points are distinct (strict monotonicity)
              (∀ i j : Fin n, i < j → pts.get i < pts.get j) ∧
              -- For n = 2, we have exactly {-1, 1}
              (n = 2 → pts.get ⟨0, sorry⟩ = -1 ∧ pts.get ⟨1, sorry⟩ = 1) ∧
              -- For n = 3, the middle point is 0
              (n = 3 → pts.get ⟨1, sorry⟩ = 0)⌝⦄ := by
  sorry
-- </vc-theorems>