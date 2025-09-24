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
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : String) (h_precond : solve_precond N) : Prop :=
  ValidOutput result ∧ (result = "Yes\n" ↔ ContainsSeven N)

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  sorry
-- </vc-theorems>