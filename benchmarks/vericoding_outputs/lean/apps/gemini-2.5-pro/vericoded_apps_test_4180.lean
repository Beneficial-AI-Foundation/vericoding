import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  1 ≤ n ∧ n ≤ 10000

def ValidChange (change : Int) : Prop :=
  0 ≤ change ∧ change ≤ 999

def CorrectChange (n : Int) (h : ValidInput n) : Int :=
  (1000 - n % 1000) % 1000

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem CorrectChange_is_ValidChange (n : Int) (h : ValidInput n) :
    ValidChange (CorrectChange n h) := by
  unfold ValidChange CorrectChange
  have h1000_pos : (1000 : Int) > 0 := by norm_num
  constructor
  · have h1000_ne_zero : (1000 : Int) ≠ 0 := by linarith [h1000_pos]
    exact Int.emod_nonneg (1000 - n % 1000) h1000_ne_zero
  · have h_lt_1000 : (1000 - n % 1000) % 1000 < 1000 := Int.emod_lt_of_pos _ h1000_pos
    linarith [h_lt_1000]
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  CorrectChange n h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (change : Int) (h_precond : solve_precond n) : Prop :=
  ValidChange change ∧ change = CorrectChange n h_precond

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · exact CorrectChange_is_ValidChange n h_precond
  · rfl
-- </vc-theorems>
