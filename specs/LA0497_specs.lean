-- <vc-preamble>

def ValidInput (a : List Int) : Prop :=
  ∀ i, 0 ≤ i ∧ i < a.length → a.get! i > 0

def CountFactorsOfTwo (n : Int) : Int :=
  if h : n > 0 ∧ n % 2 = 0 then 1 + CountFactorsOfTwo (n / 2)
  else if n > 0 then 0
  else 0
termination_by n.natAbs
decreasing_by
  simp_wf
  have : n / 2 < n := by
    have : n > 0 := h.1
    have : n % 2 = 0 := h.2
    omega
  omega

def SumFactors (a : List Int) (i : Nat) : Int :=
  if h : i < a.length then
    CountFactorsOfTwo (a.get! i) + SumFactors a (i + 1)
  else 0
termination_by a.length - i

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