-- <vc-preamble>
def ValidInput (n : Int) (sticks : List Int) : Prop :=
  1 ≤ n ∧ n ≤ 1000 ∧
  sticks.length = n ∧
  (∀ i, 0 ≤ i ∧ i < sticks.length → 1 ≤ sticks[i]! ∧ sticks[i]! ≤ 100)

def AbsInt (x : Int) : Int :=
  if x ≥ 0 then x else -x

def MaxInt (a b : Int) : Int :=
  if a ≥ b then a else b

def SumCosts (sticks : List Int) (t : Int) : List Int → Int
  | [] => 0
  | h :: tail => MaxInt 0 (AbsInt (t - h) - 1) + SumCosts sticks t tail

def CostForT (sticks : List Int) (t : Int) : Int :=
  SumCosts sticks t sticks

def IsOptimalT (sticks : List Int) (t : Int) : Prop :=
  ∀ other_t, 1 ≤ other_t ∧ other_t ≤ 99 → 
    CostForT sticks t ≤ CostForT sticks other_t

@[reducible, simp]
def solve_precond (n : Int) (sticks : List Int) : Prop :=
  ValidInput n sticks
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (sticks : List Int) (h_precond : solve_precond n sticks) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (sticks : List Int) (result : Int × Int) (h_precond : solve_precond n sticks) : Prop :=
  let t := result.1
  let min_cost := result.2
  1 ≤ t ∧ t ≤ 99 ∧
  min_cost ≥ 0 ∧
  min_cost = CostForT sticks t ∧
  IsOptimalT sticks t

theorem solve_spec_satisfied (n : Int) (sticks : List Int) (h_precond : solve_precond n sticks) :
    solve_postcond n sticks (solve n sticks h_precond) h_precond := by
  sorry
-- </vc-theorems>