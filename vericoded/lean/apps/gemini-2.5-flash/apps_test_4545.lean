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
def myabs (x : Int) : Int := if x < 0 then -x else x
-- </vc-helpers>

-- <vc-definitions>
def solve (N A : Int) (h_precond : solve_precond N A) : Int :=
  BlackSquares N A h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N A : Int) (blackSquares : Int) (h_precond : solve_precond N A) : Prop :=
  ValidOutput N A blackSquares h_precond

theorem solve_spec_satisfied (N A : Int) (h_precond : solve_precond N A) :
    solve_postcond N A (solve N A h_precond) h_precond := by
  unfold solve_postcond ValidOutput
  dsimp [solve]
  constructor
  . rfl
  . have h_NN_ge_A : N * N ≥ A := h_precond.2.2.2
    exact Int.sub_nonneg_of_le h_NN_ge_A
-- </vc-theorems>
