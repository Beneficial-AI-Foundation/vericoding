-- <vc-preamble>
def ValidInput (n d : Int) (hotels : List Int) : Prop :=
  n > 0 ∧ d > 0 ∧ hotels.length = n ∧
  (∀ i, 0 ≤ i ∧ i < n - 1 → 
    if h1 : i.natAbs < hotels.length ∧ (i + 1).natAbs < hotels.length then
      hotels[(i.natAbs)]! < hotels[((i + 1).natAbs)]!
    else False)

def SumContributions (hotels : List Int) (d : Int) (i : Int) : Int :=
  if i ≤ 0 then 0
  else
    if h : i.natAbs < hotels.length ∧ (i - 1).natAbs < hotels.length ∧ 0 ≤ i - 1 then
      let gap := hotels[(i.natAbs)]! - hotels[((i - 1).natAbs)]!
      let contribution := if gap = 2*d then 1 else if gap > 2*d then 2 else 0
      contribution + SumContributions hotels d (i-1)
    else 0
termination_by i.natAbs

def CorrectResult (n d : Int) (hotels : List Int) (result : Int) : Prop :=
  result = 2 + SumContributions hotels d (n-1) ∧ result ≥ 2

@[reducible, simp]
def solve_precond (n d : Int) (hotels : List Int) : Prop :=
  ValidInput n d hotels
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n d : Int) (hotels : List Int) (h_precond : solve_precond n d hotels) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n d : Int) (hotels : List Int) (result : Int) (h_precond : solve_precond n d hotels) : Prop :=
  CorrectResult n d hotels result

theorem solve_spec_satisfied (n d : Int) (hotels : List Int) (h_precond : solve_precond n d hotels) :
    solve_postcond n d hotels (solve n d hotels h_precond) h_precond := by
  sorry
-- </vc-theorems>