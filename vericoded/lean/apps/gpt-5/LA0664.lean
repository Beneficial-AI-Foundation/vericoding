import Mathlib
-- <vc-preamble>
def ValidInput (N : Int) : Prop :=
  1 ≤ N ∧ N ≤ 100

def TotalCost (N : Int) (h : ValidInput N) : Int :=
  800 * N

def Cashback (N : Int) (h : ValidInput N) : Int :=
  (N / 15) * 200

def NetAmount (N : Int) (h : ValidInput N) : Int :=
  TotalCost N h - Cashback N h

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma NetAmount_def (N : Int) (h : ValidInput N) :
  NetAmount N h = TotalCost N h - Cashback N h := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : Int :=
  NetAmount N h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : Int) (h_precond : solve_precond N) : Prop :=
  result = NetAmount N h_precond

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  rfl
-- </vc-theorems>
