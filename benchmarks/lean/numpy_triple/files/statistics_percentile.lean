-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def percentile {n : Nat} (arr : Vector Float (n + 1)) (q : Float) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem percentile_spec {n : Nat} (arr : Vector Float (n + 1)) (q : Float) 
    (h_valid_q : 0 ≤ q ∧ q ≤ 100) :
    ⦃⌜0 ≤ q ∧ q ≤ 100⌝⦄
    percentile arr q
    ⦃⇓result => ⌜
      -- The result is bounded by the minimum and maximum values in the array
      (∀ i : Fin (n + 1), arr.get i ≤ result → 
        ∃ j : Fin (n + 1), arr.get j ≥ result) ∧
      (∀ i : Fin (n + 1), arr.get i ≥ result → 
        ∃ j : Fin (n + 1), arr.get j ≤ result) ∧
      -- Special cases
      (q = 0 → ∀ i : Fin (n + 1), result ≤ arr.get i) ∧
      (q = 100 → ∀ i : Fin (n + 1), arr.get i ≤ result)
    ⌝⦄ := by
  sorry
-- </vc-theorems>