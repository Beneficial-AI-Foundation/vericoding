-- <vc-preamble>
partial def digitSum (n : Int) : Int :=
  if n ≤ 0 then 0
  else (n % 10) + digitSum (n / 10)

partial def sumInRange (N A B : Int) : Int :=
  if N ≤ 0 then 0
  else if A ≤ digitSum N ∧ digitSum N ≤ B then N + sumInRange (N-1) A B
  else sumInRange (N-1) A B

@[reducible, simp]
def solve_precond (N A B : Int) : Prop :=
  N ≥ 1 ∧ A ≥ 1 ∧ A ≤ B ∧ B ≤ 36
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N A B : Int) (h_precond : solve_precond N A B) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N A B : Int) (result: Int) (h_precond : solve_precond N A B) : Prop :=
  result = sumInRange N A B ∧ result ≥ 0

theorem solve_spec_satisfied (N A B : Int) (h_precond : solve_precond N A B) :
    solve_postcond N A B (solve N A B h_precond) h_precond := by
  sorry
-- </vc-theorems>