-- <vc-preamble>
@[reducible, simp]
def double_array_elements_precond (s : Array Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
def double_array_elements_aux (s_old s : Array Int) (i : Nat) : Array Int :=
  if i < s.size then
    let new_s := s.set! i (2 * (s_old[i]!))
    double_array_elements_aux s_old new_s (i + 1)
  else
    s
-- </vc-helpers>

-- <vc-definitions>
def double_array_elements (s : Array Int) (h_precond : double_array_elements_precond (s)) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def double_array_elements_postcond (s : Array Int) (result: Array Int) (h_precond : double_array_elements_precond (s)) :=
  result.size = s.size ∧ ∀ i, i < s.size → result[i]! = 2 * s[i]!

theorem double_array_elements_spec_satisfied (s: Array Int) (h_precond : double_array_elements_precond (s)) :
    double_array_elements_postcond (s) (double_array_elements (s) h_precond) h_precond := by
  sorry
-- </vc-theorems>