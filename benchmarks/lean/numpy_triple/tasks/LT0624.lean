-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def join {n : Nat} (sep seq : Vector String n) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem join_spec {n : Nat} (sep seq : Vector String n) :
    ⦃⌜True⌝⦄
    join sep seq
    ⦃⇓result => ⌜∀ i : Fin n, 
      let s := seq.get i
      let separator := sep.get i
      let expected_result := if s.length ≤ 1 then s 
                           else String.intercalate separator (s.toList.map String.singleton)
      -- Core correctness property
      result.get i = expected_result ∧
      -- Length property for non-trivial cases
      (s.length > 1 → (result.get i).length = s.length + (s.length - 1) * separator.length) ∧
      -- Empty string preservation
      (s.length = 0 → result.get i = "") ∧
      -- Single character preservation  
      (s.length = 1 → result.get i = s) ∧
      -- Non-empty result for non-empty input
      (s.length > 0 → (result.get i).length > 0)⌝⦄ := by
  sorry
-- </vc-theorems>