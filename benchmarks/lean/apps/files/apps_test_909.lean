-- <vc-preamble>
def ValidInput (a b c : Int) : Prop :=
  1 ≤ a ∧ a ≤ 10 ∧ 1 ≤ b ∧ b ≤ 10 ∧ 1 ≤ c ∧ c ≤ 10

def AllExpressions (a b c : Int) : List Int :=
  [a * b * c, a + b * c, a * b + c, a * (b + c), (a + b) * c, a + b + c]

def MaxExpression (a b c : Int) (h : ValidInput a b c) : Int :=
  let exprs := AllExpressions a b c
  if exprs[0]! ≥ exprs[1]! ∧ exprs[0]! ≥ exprs[2]! ∧ exprs[0]! ≥ exprs[3]! ∧ exprs[0]! ≥ exprs[4]! ∧ exprs[0]! ≥ exprs[5]! then exprs[0]!
  else if exprs[1]! ≥ exprs[2]! ∧ exprs[1]! ≥ exprs[3]! ∧ exprs[1]! ≥ exprs[4]! ∧ exprs[1]! ≥ exprs[5]! then exprs[1]!
  else if exprs[2]! ≥ exprs[3]! ∧ exprs[2]! ≥ exprs[4]! ∧ exprs[2]! ≥ exprs[5]! then exprs[2]!
  else if exprs[3]! ≥ exprs[4]! ∧ exprs[3]! ≥ exprs[5]! then exprs[3]!
  else if exprs[4]! ≥ exprs[5]! then exprs[4]!
  else exprs[5]!

def IsMaxOfAllExpressions (result a b c : Int) (h : ValidInput a b c) : Prop :=
  let exprs := AllExpressions a b c
  result ∈ exprs ∧ ∀ i, 0 ≤ i ∧ i < exprs.length → result ≥ exprs[i]!

@[reducible, simp]
def solve_precond (a b c : Int) : Prop :=
  ValidInput a b c
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c : Int) (h_precond : solve_precond a b c) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c : Int) (result: Int) (h_precond : solve_precond a b c) : Prop :=
  IsMaxOfAllExpressions result a b c h_precond ∧ result = MaxExpression a b c h_precond

theorem solve_spec_satisfied (a b c : Int) (h_precond : solve_precond a b c) :
    solve_postcond a b c (solve a b c h_precond) h_precond := by
  sorry
-- </vc-theorems>