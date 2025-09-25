-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebvander {n : Nat} (x : Vector Float n) (deg : Nat) : Id (Vector (Vector Float (deg + 1)) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebvander_spec {n : Nat} (x : Vector Float n) (deg : Nat) :
    ⦃⌜True⌝⦄
    chebvander x deg
    ⦃⇓V => ⌜-- T_0(x) = 1 for all x
            (∀ i : Fin n, (V.get i).get ⟨0, sorry⟩ = 1) ∧
            -- T_1(x) = x when deg ≥ 1
            (deg ≥ 1 → ∀ i : Fin n, (V.get i).get ⟨1, sorry⟩ = x.get i) ∧
            -- Recurrence relation: T_{k+1}(x) = 2x*T_k(x) - T_{k-1}(x) for k ≥ 1
            (∀ k : Nat, 1 ≤ k ∧ k < deg → 
              ∀ i : Fin n, 
                (V.get i).get ⟨k + 1, sorry⟩ = 
                  2 * (x.get i) * (V.get i).get ⟨k, sorry⟩ - 
                  (V.get i).get ⟨k - 1, sorry⟩) ∧
            -- Mathematical property: Chebyshev polynomials are bounded by 1 on [-1,1]
            (∀ i : Fin n, -1 ≤ x.get i ∧ x.get i ≤ 1 → 
              ∀ j : Fin (deg + 1), -1 ≤ (V.get i).get j ∧ (V.get i).get j ≤ 1) ∧
            -- Symmetry property: T_n(-x) = (-1)^n * T_n(x)
            (∀ i j : Fin n, x.get i = -(x.get j) → 
              ∀ k : Fin (deg + 1), 
                (V.get i).get k = (if k.val % 2 = 0 then 1 else -1) * (V.get j).get k)⌝⦄ := by
  sorry
-- </vc-theorems>