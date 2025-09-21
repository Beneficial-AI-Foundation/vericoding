-- <vc-preamble>
@[reducible]
def reverseString_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseString (s : String) (h_precond : reverseString_precond (s)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def reverseString_postcond (s : String) (result: String) (h_precond : reverseString_precond (s)) : Prop :=
  result.length = s.length ∧ result.toList = s.toList.reverse

theorem reverseString_spec_satisfied (s: String) (h_precond : reverseString_precond (s)) :
    reverseString_postcond (s) (reverseString (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>