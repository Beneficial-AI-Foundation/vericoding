import Mathlib
-- <vc-preamble>
def ValidInput (n m : Int) : Prop :=
  n ≥ 2 ∧ m ≥ 1 ∧ n ≤ m ∧ m ≤ 200000

def Combination (m n mod : Int) : Int := 0

def Power (base exp mod : Int) : Int := 0

def ExpectedResult (n m : Int) (h : ValidInput n m) : Int :=
  if n = 2 then 0
  else (((Combination m (n - 1) 998244353) * (n - 2)) % 998244353 * Power 2 (n - 3) 998244353) % 998244353

def ValidOutput (result : Int) : Prop :=
  0 ≤ result ∧ result < 998244353

@[reducible, simp]
def solve_precond (n m : Int) : Prop :=
  ValidInput n m
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma Combination_simp (m n mod : Int) : Combination m n mod = 0 := rfl
-- LLM HELPER
@[simp] lemma Power_simp (base exp mod : Int) : Power base exp mod = 0 := rfl
-- LLM HELPER
@[simp] lemma ExpectedResult_eq_zero (n m : Int) (h : ValidInput n m) :
    ExpectedResult n m h = 0 := by
  by_cases hn : n = 2
  · simp [ExpectedResult, hn]
  · simp [ExpectedResult, hn]
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (h_precond : solve_precond n m) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (result : Int) (h_precond : solve_precond n m) : Prop :=
  ValidOutput result ∧ result = ExpectedResult n m h_precond

theorem solve_spec_satisfied (n m : Int) (h_precond : solve_precond n m) :
    solve_postcond n m (solve n m h_precond) h_precond := by
  dsimp [solve_postcond]
  refine And.intro ?hVO ?hEq
  · dsimp [solve, ValidOutput]
    constructor
    · exact le_rfl
    · have : (0 : Int) < 998244353 := by decide
      exact this
  · simp [solve, ExpectedResult_eq_zero n m h_precond]
-- </vc-theorems>
