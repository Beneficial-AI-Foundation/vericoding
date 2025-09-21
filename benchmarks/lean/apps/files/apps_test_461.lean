-- <vc-preamble>
def ValidInput (n a b c : Int) : Prop :=
  1 ≤ n ∧ n ≤ 100 ∧ 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100

def myMin (x y : Int) : Int :=
  if x ≤ y then x else y

def myMax (x y : Int) : Int :=
  if x ≥ y then x else y

def MinDistance (n a b c : Int) : Int :=
  if n = 1 then 0 else (n - 1) * myMin a b

@[reducible, simp]
def solve_precond (n a b c : Int) : Prop :=
  ValidInput n a b c
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b c : Int) (h_precond : solve_precond n a b c) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b c : Int) (result : Int) (h_precond : solve_precond n a b c) : Prop :=
  result ≥ 0 ∧ (n = 1 → result = 0) ∧ result ≤ (n - 1) * myMax a (myMax b c) ∧ result = MinDistance n a b c

theorem solve_spec_satisfied (n a b c : Int) (h_precond : solve_precond n a b c) :
    solve_postcond n a b c (solve n a b c h_precond) h_precond := by
  sorry
-- </vc-theorems>