-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def startswith {n : Nat} (a : Vector String n) (prefixes : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem startswith_spec {n : Nat} (a : Vector String n) (prefixes : Vector String n) :
    ⦃⌜True⌝⦄
    startswith a prefixes
    ⦃⇓r => ⌜∀ i : Fin n, 
      -- Main specification: result matches String.startsWith for each pair
      (r.get i = (a.get i).startsWith (prefixes.get i)) ∧
      -- Mathematical property: if result is true, prefix appears at the beginning
      (r.get i = true → 
        (prefixes.get i).length ≤ (a.get i).length ∧
        (a.get i).take (prefixes.get i).length = (prefixes.get i)) ∧
      -- Mathematical property: if result is false, prefix does not appear at the beginning
      (r.get i = false → 
        (prefixes.get i).length > (a.get i).length ∨
        (a.get i).take (prefixes.get i).length ≠ (prefixes.get i))⌝⦄ := by
  sorry
-- </vc-theorems>