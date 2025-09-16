-- <vc-preamble>
def ValidInput (a : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < a.length → a[i]! > 0

def CountFactorsOfTwo (n : Int) : Int :=
  if h : n > 0 then
    if n % 2 = 0 then 1 + CountFactorsOfTwo (n / 2)
    else 0
  else 0
termination_by n
decreasing_by
  simp_wf
  sorry

def SumFactors (a : List Int) (i : Nat) : Int :=
  if h : i < a.length then 
    CountFactorsOfTwo (a[i]!) + SumFactors a (i + 1)
  else 0
termination_by a.length - i
decreasing_by
  simp_wf
  omega

def MaxOperations (a : List Int) : Int :=
  SumFactors a 0

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  ValidInput a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result : Int) (h_precond : solve_precond a) : Prop :=
  result ≥ 0 ∧ result = MaxOperations a

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  sorry
-- </vc-theorems>
