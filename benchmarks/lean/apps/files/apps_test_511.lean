-- <vc-preamble>
def ValidInput (input : String) : Prop :=
  input.length > 0 ∧
  (∃ i, i < input.length ∧ input.data[i]? = some ' ') ∧
  (∀ j, j < input.length → 
    let c := input.data[j]!
    ('0' ≤ c ∧ c ≤ '9') ∨ c = ' ' ∨ c = '\n')

def gcd (a b : Nat) : Nat :=
  if a = 0 then b
  else if b = 0 then a
  else if a > b then gcd (a - b) b
  else gcd a (b - a)
termination_by a + b

partial def f_mathematical (x y : Nat) : Nat :=
  if y = 0 then 0
  else 
    let g := gcd x y
    if g ≥ y then 1
    else 1 + f_mathematical x (y - g)

def ValidOutput (result : String) : Prop :=
  result.length > 0 ∧
  (∀ i, i < result.length → 
    let c := result.data[i]!
    ('0' ≤ c ∧ c ≤ '9') ∨ c = '\n') ∧
  (result.length > 0 → result.data[result.length - 1]! = '\n')

@[reducible, simp]
def solve_precond (input : String) : Prop :=
  ValidInput input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (input : String) (h_precond : solve_precond input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (input : String) (result : String) (h_precond : solve_precond input) : Prop :=
  ValidOutput result

theorem solve_spec_satisfied (input : String) (h_precond : solve_precond input) :
    solve_postcond input (solve input h_precond) h_precond := by
  sorry
-- </vc-theorems>