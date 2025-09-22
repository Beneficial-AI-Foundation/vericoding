-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def endswith {n : Nat} (a : Vector String n) (suffix : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem endswith_spec {n : Nat} (a : Vector String n) (suffix : Vector String n) :
    ⦃⌜True⌝⦄
    endswith a suffix
    ⦃⇓r => ⌜∀ i : Fin n, 
      -- Main specification: result matches String.endsWith for each pair
      (r.get i = (a.get i).endsWith (suffix.get i)) ∧
      -- Mathematical property: if result is true, suffix appears at the end
      (r.get i = true → 
        (suffix.get i).length ≤ (a.get i).length ∧
        (a.get i).drop ((a.get i).length - (suffix.get i).length) = (suffix.get i)) ∧
      -- Mathematical property: if result is false, suffix does not appear at the end
      (r.get i = false → 
        (suffix.get i).length > (a.get i).length ∨
        (a.get i).drop ((a.get i).length - (suffix.get i).length) ≠ (suffix.get i))⌝⦄ := by
  sorry
-- </vc-theorems>