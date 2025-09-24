-- <vc-preamble>
partial def ProductOfDigits (x : Int) : Int :=
  if x = 0 then 1
  else if x < 10 then x
  else (x % 10) * ProductOfDigits (x / 10)

partial def MaxProductOfDigitsInRange (n : Int) : Int :=
  if n = 1 then 1
  else
    let current := ProductOfDigits n
    let rest := MaxProductOfDigitsInRange (n - 1)
    if current > rest then current else rest

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  n ≥ 1
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
  result = MaxProductOfDigitsInRange n ∧
  result ≥ 1 ∧
  (∀ k, 1 ≤ k ∧ k ≤ n → ProductOfDigits k ≤ result) ∧
  (∃ k, 1 ≤ k ∧ k ≤ n ∧ ProductOfDigits k = result)

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>