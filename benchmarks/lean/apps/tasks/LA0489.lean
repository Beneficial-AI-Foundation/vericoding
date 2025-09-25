-- <vc-preamble>
def ValidInput (N M : Int) (A : List Int) : Prop :=
  N ≥ 0 ∧ M ≥ 0 ∧ M = A.length

def sum (s : List Int) : Int :=
  s.sum

def CanCompleteAllAssignments (N : Int) (A : List Int) : Prop :=
  sum A ≤ N

def TotalAssignmentDays (A : List Int) : Int :=
  sum A

@[reducible, simp]
def solve_precond (N M : Int) (A : List Int) : Prop :=
  ValidInput N M A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N M : Int) (A : List Int) (h_precond : solve_precond N M A) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N M : Int) (A : List Int) (result : Int) (h_precond : solve_precond N M A) : Prop :=
  (M = 0 → result = N) ∧
  (M > 0 ∧ CanCompleteAllAssignments N A → result = N - TotalAssignmentDays A) ∧
  (M > 0 ∧ ¬CanCompleteAllAssignments N A → result = -1) ∧
  result ≥ -1

theorem solve_spec_satisfied (N M : Int) (A : List Int) (h_precond : solve_precond N M A) :
    solve_postcond N M A (solve N M A h_precond) h_precond := by
  sorry
-- </vc-theorems>