-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_rint {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_rint_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_rint x
    ⦃⇓result => ⌜∀ i : Fin n,
      -- The result is the nearest integer (as a float)
      (∃ k : Int, result.get i = Float.ofInt k) ∧
      -- The difference is at most 0.5
      (Float.abs (result.get i - x.get i) ≤ 0.5) ∧
      -- If x[i] is already an integer, it remains unchanged
      (∃ k : Int, x.get i = Float.ofInt k → result.get i = x.get i) ∧
      -- For ties, round to even (this is the IEEE 754 rule)
      (∀ k : Int, x.get i = Float.ofInt k + 0.5 → 
        (k % 2 = 0 → result.get i = Float.ofInt k) ∧
        (k % 2 = 1 → result.get i = Float.ofInt (k + 1)))⌝⦄ := by
  sorry
-- </vc-theorems>