import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 2

def IsWinForWhite (n : Int) : Prop :=
  n % 2 = 0

def IsWinForBlack (n : Int) : Prop :=
  n % 2 = 1

instance (n : Int) : Decidable (IsWinForBlack n) := by
  unfold IsWinForBlack
  infer_instance

def OptimalWhiteMove (n : Int) : Int × Int :=
  (1, 2)

def ValidResult (n : Int) (result : String) : Prop :=
  if IsWinForBlack n then
    result = "black\n"
  else
    result = "white\n1 2\n"

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem ValidResult_eval_black (n : Int) {result : String}
    (h : IsWinForBlack n) :
    ValidResult n result = (result = "black\n") := by
  simp [ValidResult, h]

-- LLM HELPER
@[simp] theorem ValidResult_eval_white (n : Int) {result : String}
    (h : ¬ IsWinForBlack n) :
    ValidResult n result = (result = "white\n1 2\n") := by
  simp [ValidResult, h]
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : String :=
  if IsWinForBlack n then "black\n" else "white\n1 2\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : String) (h_precond : solve_precond n) : Prop :=
  ValidResult n result

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  by_cases h : IsWinForBlack n
  · simp [solve_postcond, solve, ValidResult, h]
  · simp [solve_postcond, solve, ValidResult, h]
-- </vc-theorems>
