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
-- LLM HELPER Helper lemmas for arithmetic operations
lemma TotalCost_eq (N : Int) (h : ValidInput N) : TotalCost N h = 800 * N := by rfl

lemma Cashback_eq (N : Int) (h : ValidInput N) : Cashback N h = (N / 15) * 200 := by rfl

lemma NetAmount_eq (N : Int) (h : ValidInput N) : NetAmount N h = TotalCost N h - Cashback N h := by rfl

-- LLM HELPER Lemma about NetAmount computation
lemma NetAmount_computation (N : Int) (h : ValidInput N) : 
    NetAmount N h = 800 * N - (N / 15) * 200 := by
  rw [NetAmount_eq, TotalCost_eq, Cashback_eq]
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
  rw [solve_postcond, solve]
-- </vc-theorems>
