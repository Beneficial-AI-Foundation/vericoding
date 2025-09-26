-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isspace {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isspace_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isspace a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (a.get i ≠ "" ∧ (a.get i).toList.all fun c => c.isWhitespace) ∧
                 -- Sanity check: Empty strings return false
                 (a.get i = "" → result.get i = false) ∧
                 -- Mathematical property: Result is boolean (trivially true but explicit)
                 (result.get i = true ∨ result.get i = false)⌝⦄ := by
  sorry
-- </vc-theorems>