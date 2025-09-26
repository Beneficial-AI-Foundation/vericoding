import Mathlib
-- <vc-preamble>
def ValidRating (R : Int) : Prop :=
  0 ≤ R ∧ R ≤ 4208

def ContestForRating (R : Int) : String :=
  if R < 1200 then "ABC\n"
  else if R < 2800 then "ARC\n" 
  else "AGC\n"

@[reducible, simp]
def solve_precond (R : Int) : Prop :=
  ValidRating R
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def solve (R : Int) (h_precond : solve_precond R) : String :=
  ContestForRating R
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (R : Int) (result : String) (h_precond : solve_precond R) : Prop :=
  result = ContestForRating R ∧
  (R < 1200 → result = "ABC\n") ∧
  (1200 ≤ R ∧ R < 2800 → result = "ARC\n") ∧
  (R ≥ 2800 → result = "AGC\n")

theorem solve_spec_satisfied (R : Int) (h_precond : solve_precond R) :
    solve_postcond R (solve R h_precond) h_precond := by
  unfold solve solve_postcond ContestForRating
  constructor
  · simp
  constructor
  · intro h_lt_1200
    simp [h_lt_1200]
  constructor
  · intro ⟨h_ge_1200, h_lt_2800⟩
    simp [not_lt.mpr h_ge_1200, h_lt_2800]
  · intro h_ge_2800
    simp [not_lt.mpr (le_trans (by norm_num : (1200 : Int) ≤ 2800) h_ge_2800), not_lt.mpr h_ge_2800]
-- </vc-theorems>
