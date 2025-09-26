-- <vc-preamble>
def ValidInput (l r : Int) : Prop :=
  l < r ∧ (r - l) % 2 = 1

def gcd (a b : Int) : Int :=
  if a = 0 then if b ≥ 0 then b else -b
  else if a > 0 then Int.gcd a.natAbs b.natAbs
  else Int.gcd a.natAbs b.natAbs

def int_to_string (n : Int) : String :=
  toString n

def PairHasGcdOne (pair : String) (l r : Int) : Prop :=
  ∃ i j, l ≤ i ∧ i ≤ r ∧ l ≤ j ∧ j ≤ r ∧ i ≠ j ∧
    pair = int_to_string i ++ " " ++ int_to_string j ∧
    (i ≠ 0 ∨ j ≠ 0) ∧ gcd i j = 1

def ValidSolution (result : List String) (l r : Int) : Prop :=
  result.length ≥ 1 ∧
  result[0]! = "YES" ∧
  result.length = 1 + (r - l + 1) / 2 ∧
  (∀ i, 1 ≤ i ∧ i < result.length → PairHasGcdOne result[i]! l r)

@[reducible, simp]
def solve_precond (l r : Int) : Prop :=
  ValidInput l r
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (l r : Int) (h_precond : solve_precond l r) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (l r : Int) (result : List String) (h_precond : solve_precond l r) : Prop :=
  ValidSolution result l r ∧
  result.length ≥ 1 ∧
  result[0]! = "YES" ∧
  result.length = 1 + (r - l + 1) / 2 ∧
  (∀ i, 1 ≤ i ∧ i < result.length →
    (∃ j, l ≤ j ∧ j ≤ r - 1 ∧ j % 2 = l % 2 ∧
     result[i]! = int_to_string j ++ " " ++ int_to_string (j + 1)))

theorem solve_spec_satisfied (l r : Int) (h_precond : solve_precond l r) :
    solve_postcond l r (solve l r h_precond) h_precond := by
  sorry
-- </vc-theorems>