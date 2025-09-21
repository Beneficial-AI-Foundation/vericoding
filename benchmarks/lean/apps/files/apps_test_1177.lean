-- <vc-preamble>
def ValidInput (N S : Int) (A : List Int) : Prop :=
  N ≥ 1 ∧ S ≥ 1 ∧ A.length = N.natAbs ∧ N ≤ 3000 ∧ S ≤ 3000 ∧
  ∀ i, 0 ≤ i ∧ i < N → A[i.natAbs]! ≥ 1 ∧ A[i.natAbs]! ≤ 3000

def ValidResult (result : Int) : Prop :=
  result ≥ 0 ∧ result < 998244353

def AllElementsGreaterThanS (A : List Int) (S : Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < A.length → A[i]! > S

def SingleElementCase (N S : Int) (A : List Int) : Int :=
  if N = 1 ∧ A.length = 1 then
    if S = A[0]! then 1 else 0
  else 0

@[reducible, simp]
def solve_precond (N S : Int) (A : List Int) : Prop :=
  ValidInput N S A
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N S : Int) (A : List Int) (h_precond : solve_precond N S A) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N S : Int) (A : List Int) (result : Int) (h_precond : solve_precond N S A) : Prop :=
  ValidResult result ∧ 
  result % 998244353 = result ∧
  (N = 1 ∧ S = A[0]! → result = SingleElementCase N S A) ∧
  (N = 1 ∧ S ≠ A[0]! → result = SingleElementCase N S A) ∧
  (AllElementsGreaterThanS A S → result = 0)

theorem solve_spec_satisfied (N S : Int) (A : List Int) (h_precond : solve_precond N S A) :
    solve_postcond N S A (solve N S A h_precond) h_precond := by
  sorry
-- </vc-theorems>