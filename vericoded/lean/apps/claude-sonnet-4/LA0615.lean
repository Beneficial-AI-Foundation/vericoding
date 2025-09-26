import Mathlib
-- <vc-preamble>
def ValidInput (N A : Int) : Prop :=
  1 ≤ N ∧ N ≤ 100 ∧ 0 ≤ A ∧ A ≤ N * N

def BlackSquares (N A : Int) (h : ValidInput N A) : Int :=
  N * N - A

def ValidOutput (N A result : Int) (h : ValidInput N A) : Prop :=
  result = BlackSquares N A h ∧ result ≥ 0

@[reducible, simp]
def solve_precond (N A : Int) : Prop :=
  ValidInput N A
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Basic arithmetic facts for the proof
lemma blacksquares_nonneg (N A : Int) (h : ValidInput N A) : BlackSquares N A h ≥ 0 := by
  unfold BlackSquares ValidInput at *
  omega
-- </vc-helpers>

-- <vc-definitions>
def solve (N A : Int) (h_precond : solve_precond N A) : Int :=
  N * N - A
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N A : Int) (blackSquares : Int) (h_precond : solve_precond N A) : Prop :=
  ValidOutput N A blackSquares h_precond

theorem solve_spec_satisfied (N A : Int) (h_precond : solve_precond N A) :
    solve_postcond N A (solve N A h_precond) h_precond := by
  unfold solve_postcond ValidOutput solve BlackSquares
  constructor
  · rfl
  · exact blacksquares_nonneg N A h_precond
-- </vc-theorems>
