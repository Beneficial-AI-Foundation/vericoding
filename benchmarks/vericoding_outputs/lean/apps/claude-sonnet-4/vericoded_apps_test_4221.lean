import Mathlib
-- <vc-preamble>
def ValidInput (s : String) : Prop :=
  s.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < s.length → 'a' ≤ s.data[i]! ∧ s.data[i]! ≤ 'z'

def CorrectPlural (s : String) (result : String) : Prop :=
  if s.length > 0 ∧ s.data[s.length - 1]! = 's' then
    result = s ++ "es"
  else
    result = s ++ "s"

@[reducible, simp]
def solve_precond (s : String) : Prop :=
  ValidInput s
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma string_ends_with_s_cases (s : String) (h_len : s.length > 0) :
  (s.length > 0 ∧ s.data[s.length - 1]! = 's') ∨ ¬(s.length > 0 ∧ s.data[s.length - 1]! = 's') := by
  classical
  exact Classical.em _
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (h_precond : solve_precond s) : String :=
  if s.length > 0 ∧ s.data[s.length - 1]! = 's' then
  s ++ "es"
else
  s ++ "s"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (s : String) (result : String) (h_precond : solve_precond s) : Prop :=
  CorrectPlural s result

theorem solve_spec_satisfied (s : String) (h_precond : solve_precond s) :
    solve_postcond s (solve s h_precond) h_precond := by
  unfold solve_postcond CorrectPlural solve
  split_ifs with h
  · rfl
  · rfl
-- </vc-theorems>
