-- <vc-preamble>
def sum_squares (p : Int) (a : List Int) : Int :=
  match a with
  | [] => 0
  | x :: xs => (p - x) * (p - x) + sum_squares p xs

def ValidInput (n : Int) (a : List Int) : Prop :=
  n ≥ 1 ∧ n ≤ 100 ∧ a.length = n ∧ 
  ∀ i, 0 ≤ i ∧ i < a.length → -100 ≤ a[i]! ∧ a[i]! ≤ 100

def IsOptimalCost (result : Int) (a : List Int) : Prop :=
  result ≥ 0 ∧
  ∃ p, -100 ≤ p ∧ p ≤ 100 ∧ result = sum_squares p a ∧
  ∀ p, -100 ≤ p ∧ p ≤ 100 → result ≤ sum_squares p a

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
  IsOptimalCost result a

theorem solve_spec_satisfied (n : Int) (a : List Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  sorry
-- </vc-theorems>