-- <vc-preamble>
def ValidInput (m d : Int) : Prop :=
  1 ≤ m ∧ m ≤ 12 ∧ 1 ≤ d ∧ d ≤ 7

def DaysInMonth (m : Int) : Int :=
  if m = 1 then 31
  else if m = 2 then 28
  else if m = 3 then 31
  else if m = 4 then 30
  else if m = 5 then 31
  else if m = 6 then 30
  else if m = 7 then 31
  else if m = 8 then 31
  else if m = 9 then 30
  else if m = 10 then 31
  else if m = 11 then 30
  else 31

def ColumnsNeeded (m d : Int) : Int :=
  1 + (d - 1 + DaysInMonth m - 1) / 7

@[reducible, simp]
def solve_precond (m d : Int) : Prop :=
  ValidInput m d
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (m d : Int) (h_precond : solve_precond m d) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (m d : Int) (result : Int) (h_precond : solve_precond m d) : Prop :=
  result = ColumnsNeeded m d ∧ 4 ≤ result ∧ result ≤ 6

theorem solve_spec_satisfied (m d : Int) (h_precond : solve_precond m d) :
    solve_postcond m d (solve m d h_precond) h_precond := by
  sorry
-- </vc-theorems>