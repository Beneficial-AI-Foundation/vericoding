import Mathlib
-- <vc-preamble>
def ValidInput (x : Int) : Prop :=
  1 ≤ x ∧ x ≤ 3000

def CorrectOutput (x : Int) (result : String) : Prop :=
  (x < 1200 → result = "ABC\n") ∧ (x ≥ 1200 → result = "ARC\n")

@[reducible, simp]
def solve_precond (x : Int) : Prop :=
  ValidInput x
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma for case analysis on the threshold
lemma threshold_cases (x : Int) : x < 1200 ∨ x ≥ 1200 := by
  omega

-- LLM HELPER: Simplification lemmas for the conditional logic
lemma solve_lt_case (x : Int) (h : x < 1200) (h_precond : solve_precond x) :
    (if x < 1200 then "ABC\n" else "ARC\n") = "ABC\n" := by
  simp [h]

lemma solve_ge_case (x : Int) (h : x ≥ 1200) (h_precond : solve_precond x) :
    (if x < 1200 then "ABC\n" else "ARC\n") = "ARC\n" := by
  simp [h]
-- </vc-helpers>

-- <vc-definitions>
def solve (x : Int) (h_precond : solve_precond x) : String :=
  if x < 1200 then "ABC\n" else "ARC\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x : Int) (result : String) (h_precond : solve_precond x) : Prop :=
  CorrectOutput x result

theorem solve_spec_satisfied (x : Int) (h_precond : solve_precond x) :
    solve_postcond x (solve x h_precond) h_precond := by
  unfold solve_postcond CorrectOutput solve
  constructor
  · intro h_lt
    exact solve_lt_case x h_lt h_precond
  · intro h_ge
    exact solve_ge_case x h_ge h_precond
-- </vc-theorems>
