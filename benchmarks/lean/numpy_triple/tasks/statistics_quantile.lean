-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def quantile {n : Nat} (a : Vector Float (n + 1)) (q : Float) 
    (h_valid : 0 ≤ q ∧ q ≤ 1) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem quantile_spec {n : Nat} (a : Vector Float (n + 1)) (q : Float) 
    (h_valid : 0 ≤ q ∧ q ≤ 1) :
    ⦃⌜0 ≤ q ∧ q ≤ 1⌝⦄
    quantile a q h_valid
    ⦃⇓result => ⌜
      -- The result is within the range of the input data
      (∃ i : Fin (n + 1), a.get i ≤ result) ∧
      (∃ i : Fin (n + 1), result ≤ a.get i) ∧
      -- For 0-quantile, result should be ≤ minimum
      (q = 0 → ∀ i : Fin (n + 1), result ≤ a.get i) ∧
      -- For 1-quantile, result should be ≥ maximum  
      (q = 1 → ∀ i : Fin (n + 1), a.get i ≤ result)⌝⦄ := by
  sorry
-- </vc-theorems>