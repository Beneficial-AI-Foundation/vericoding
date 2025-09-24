-- <vc-preamble>
def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ a.length = n.natAbs ∧ ∀ i, 0 ≤ i ∧ i < n → a[i.natAbs]? ≠ none ∧ a[i.natAbs]?.get! ≥ 0

def CountSurvivorsFrom (n : Int) (a : List Int) (start : Int) (left : Int) : Int :=
  if h : start ≥ n then 0
  else
    let i := n - 1 - start
    let survives := if i < left then 1 else 0
    let aVal := if h : i.natAbs < a.length then a[i.natAbs] else 0
    let newLeft := if i - aVal < left then i - aVal else left
    survives + CountSurvivorsFrom n a (start + 1) newLeft
termination_by (n - start).natAbs
decreasing_by
  simp_wf
  omega

def CountSurvivors (n : Int) (a : List Int) : Int :=
  CountSurvivorsFrom n a 0 n

@[reducible, simp]
def solve_precond (n : Int) (a : List Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (a : List Int) (h_precond : solve_precond n a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (a : List Int) (result : Int) (h_precond : solve_precond n a) : Prop :=
  result ≥ 0 ∧ result ≤ n ∧ result = CountSurvivors n a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>