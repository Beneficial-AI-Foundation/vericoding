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
-- No additional helper definitions are required for this simple indexing solution.
-- This comment placeholder keeps the <vc-helpers> section syntactically valid.
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
  simp [solve]
-- </vc-theorems>
