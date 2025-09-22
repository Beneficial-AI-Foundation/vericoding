-- <vc-preamble>
@[reducible, simp]
def containsZ_precond (s : String) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsZ (s : String) (h_precond : containsZ_precond (s)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def containsZ_postcond (s : String) (result: Bool) (h_precond : containsZ_precond (s)) :=
  let cs := s.toList
  (∃ x, x ∈ cs ∧ (x = 'z' ∨ x = 'Z')) ↔ result

theorem containsZ_spec_satisfied (s: String) (h_precond : containsZ_precond (s)) :
    containsZ_postcond (s) (containsZ (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>