-- <vc-preamble>
-- <vc-preamble>
def ValidInput (values : List Int) : Prop :=
  values.length ≥ 1 ∧ ∀ i, 0 ≤ i ∧ i < values.length → values[i]! > 0

def gcd (a b : Int) : Int := sorry

def gcdSeq (values : List Int) (index : Int) (current : Int) : Int := sorry

def gcdOfAll (values : List Int) : Int := 
  if h : values.length ≥ 1 then gcdSeq values 1 values[0]! else 1

@[reducible, simp]
def solve_precond (values : List Int) : Prop :=
  ValidInput values
-- </vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- <vc-definitions>
def solve (values : List Int) (h_precond : solve_precond values) : Int :=
  sorry
-- </vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
-- <vc-theorems>
@[reducible, simp]
def solve_postcond (values : List Int) (result : Int) (h_precond : solve_precond values) : Prop :=
  result > 0 ∧ 
  result = gcdOfAll values ∧ 
  (∀ i, 0 ≤ i ∧ i < values.length → values[i]! % result = 0)

theorem solve_spec_satisfied (values : List Int) (h_precond : solve_precond values) :
    solve_postcond values (solve values h_precond) h_precond := by
  sorry
-- </vc-theorems>
-- </vc-theorems>
