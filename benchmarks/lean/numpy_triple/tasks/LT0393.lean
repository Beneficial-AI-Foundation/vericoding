-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chebpts1 (n : Nat) (h : n > 0) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chebpts1_spec (n : Nat) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    chebpts1 n h
    ⦃⇓result => ⌜(∀ k : Fin n, 
                  result.get k = Float.cos (3.141592653589793 * (k.val.toFloat + 0.5) / n.toFloat)) ∧
                 (∀ i j : Fin n, i < j → result.get i > result.get j) ∧
                 (∀ k : Fin n, -1 ≤ result.get k ∧ result.get k ≤ 1) ∧
                 (∀ k : Fin n, k.val + 1 ≤ n → 
                  result.get k = -result.get ⟨n - 1 - k.val, sorry⟩)⌝⦄ := by
  sorry
-- </vc-theorems>