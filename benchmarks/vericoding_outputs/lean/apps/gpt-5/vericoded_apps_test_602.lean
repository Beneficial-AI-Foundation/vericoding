import Mathlib
-- <vc-preamble>
def ValidInput (a : Int) : Prop :=
  1 ≤ a ∧ a ≤ 40

def Presidents : List String :=
  ["Washington", "Adams", "Jefferson", "Madison", "Monroe", "Adams", "Jackson", 
   "Van Buren", "Harrison", "Tyler", "Polk", "Taylor", "Fillmore", "Pierce", 
   "Buchanan", "Lincoln", "Johnson", "Grant", "Hayes", "Garfield", "Arthur", 
   "Cleveland", "Harrison", "Cleveland", "McKinley", "Roosevelt", "Taft", 
   "Wilson", "Harding", "Coolidge", "Hoover", "Roosevelt", "Truman", 
   "Eisenhower", "Kennedy", "Johnson", "Nixon", "Ford", "Carter", "Reagan"]

@[reducible, simp]
def solve_precond (a : Int) : Prop :=
  ValidInput a
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def indexOfInt (a : Int) : Nat := a.natAbs - 1

-- LLM HELPER
@[simp] theorem indexOfInt_def (a : Int) : indexOfInt a = a.natAbs - 1 := rfl

-- LLM HELPER
theorem presidents_length_eq : Presidents.length = 40 := by
  decide

-- LLM HELPER
theorem presidents_length_pos : 0 < Presidents.length := by
  decide
-- </vc-helpers>

-- <vc-definitions>
def solve (a : Int) (h_precond : solve_precond a) : String :=
  Presidents[a.natAbs - 1]!
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : Int) (result : String) (h_precond : solve_precond a) : Prop :=
  result = Presidents[a.natAbs - 1]!

theorem solve_spec_satisfied (a : Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  rfl
-- </vc-theorems>
