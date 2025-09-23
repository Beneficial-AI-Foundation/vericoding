-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def typecodes (category : String) : Id (Option String) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem typecodes_spec (category : String) :
    ⦃⌜True⌝⦄
    typecodes category
    ⦃⇓result => ⌜
      (category = "Character" → result = some "S1") ∧
      (category = "Integer" → result = some "bhilqnp") ∧
      (category = "UnsignedInteger" → result = some "BHILQNP") ∧
      (category = "Float" → result = some "fdg") ∧
      (category = "Complex" → result = some "FDG") ∧
      (category = "AllInteger" → result = some "bBhHiIlLqQnNpP") ∧
      (category = "AllFloat" → result = some "fdgFDG") ∧
      (category = "Datetime" → result = some "Mm") ∧
      (category = "All" → result = some "?bhilqnpBHILQNPfdgFDGSUVOMm") ∧
      (category ∉ ["Character", "Integer", "UnsignedInteger", "Float", "Complex", "AllInteger", "AllFloat", "Datetime", "All"] → result = none)
    ⌝⦄ := by
  sorry
-- </vc-theorems>