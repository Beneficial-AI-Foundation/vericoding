-- <vc-preamble>
def ValidInput (n : Int) : Prop :=
  n ≥ 1

def DivisibleByBoth (result : Int) (n : Int) : Prop :=
  result % 2 = 0 ∧ result % n = 0

def IsSmallest (result : Int) (n : Int) : Prop :=
  ∀ k, 1 ≤ k ∧ k < result → ¬(k % 2 = 0 ∧ k % n = 0)

def LCM (a : Int) (b : Int) : Int :=
  if a % b = 0 then a
  else if b % a = 0 then b
  else a * b

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : Int) (h_precond : solve_precond n) : Prop :=
  result ≥ 1 ∧ 
  DivisibleByBoth result n ∧ 
  IsSmallest result n ∧ 
  (n % 2 = 0 → result = n) ∧ (n % 2 ≠ 0 → result = n * 2)

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>