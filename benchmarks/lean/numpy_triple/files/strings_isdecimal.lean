-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isdecimal {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isdecimal_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isdecimal a
    ⦃⇓result => ⌜∀ i : Fin n, 
        (result.get i = true ↔ 
            ((a.get i).length > 0 ∧ 
             ∀ c : Char, c ∈ (a.get i).toList → c.isDigit = true)) ∧
        -- Empty string property: empty strings always return false
        (a.get i = "" → result.get i = false)⌝⦄ := by
  sorry
-- </vc-theorems>