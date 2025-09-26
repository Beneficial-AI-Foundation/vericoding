import Mathlib
-- <vc-preamble>
def ValidInput (N : Int) : Prop :=
  100 ≤ N ∧ N ≤ 999

def ContainsSeven (N : Int) : Prop :=
  (N % 10) = 7 ∨ ((N / 10) % 10) = 7 ∨ (N / 100) = 7

def ValidOutput (result : String) : Prop :=
  result = "Yes\n" ∨ result = "No\n"

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- This problem is simple enough that no helper definitions are required.
-- The implementation of `solve` can directly mirror the logic in `ContainsSeven`,
-- and the proof can be handled with standard tactics.
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : String :=
  if (N % 10 = 7) ∨ ((N / 10) % 10 = 7) ∨ (N / 100 = 7) then
    "Yes\n"
  else
    "No\n"
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : String) (h_precond : solve_precond N) : Prop :=
  ValidOutput result ∧ (result = "Yes\n" ↔ ContainsSeven N)

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  simp only [solve, solve_postcond, ContainsSeven, ValidOutput]
  split_ifs with h_contains <;> simp [*]
-- </vc-theorems>
