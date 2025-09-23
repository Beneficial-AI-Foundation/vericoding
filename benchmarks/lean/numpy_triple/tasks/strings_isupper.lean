-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isupper {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isupper_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isupper a
    ⦃⇓result => ⌜∀ i : Fin n, 
                   let s := a.get i
                   let chars := s.toList
                   result.get i = (chars.length > 0 ∧ 
                                  (∃ c ∈ chars, c.isAlpha) ∧
                                  (∀ c ∈ chars, c.isAlpha → c.isUpper))⌝⦄ := by
  sorry
-- </vc-theorems>