-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def capitalize {n : Nat} (a : Vector String n) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem capitalize_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    capitalize a
    ⦃⇓r => ⌜∀ i : Fin n,
      let original := a.get i
      let result := r.get i
      -- Length preservation: result has same length as original
      (result.length = original.length) ∧
      -- Empty string case: empty input produces empty output
      (original.length = 0 → result = "") ∧
      -- Core property: the result is the capitalized version of the original
      (result = original.capitalize) ∧
      -- Idempotence property: capitalizing a capitalized string doesn't change it
      (result.capitalize = result) ∧
      -- Sanity check: applying capitalize to empty string gives empty string
      (original = "" → result = "") ∧
      -- Mathematical property: the operation is deterministic
      (result = original.capitalize)⌝⦄ := by
  sorry
-- </vc-theorems>