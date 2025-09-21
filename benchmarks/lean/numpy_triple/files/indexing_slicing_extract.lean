-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def extract {n k : Nat} (condition : Vector Bool n) (arr : Vector Float n) 
    (h : k = (condition.toArray.toList.count true)) : Id (Vector Float k) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem extract_spec {n k : Nat} (condition : Vector Bool n) (arr : Vector Float n) 
    (h : k = (condition.toArray.toList.count true)) :
    ⦃⌜k = (condition.toArray.toList.count true)⌝⦄
    extract condition arr h
    ⦃⇓result => 
      -- The result contains exactly the elements from arr where condition is True
      ⌜∀ i : Fin k, ∃ idx : Fin n, condition.get idx = true ∧ result.get i = arr.get idx⌝
    ⦄ := by
  sorry
-- </vc-theorems>