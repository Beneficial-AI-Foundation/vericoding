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
-- LLM HELPER: Convert Int to Nat safely given precondition
def int_to_nat_valid (a : Int) (h : ValidInput a) : Nat :=
  a.natAbs

-- LLM HELPER: Lemma that valid input gives valid list index
lemma valid_index (a : Int) (h : ValidInput a) : a.natAbs - 1 < Presidents.length := by
  unfold ValidInput at h
  simp [Presidents]
  omega
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
  unfold solve_postcond solve
  rfl
-- </vc-theorems>
