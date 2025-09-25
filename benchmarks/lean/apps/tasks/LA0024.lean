-- <vc-preamble>
def power (base : Int) (exp : Nat) : Int :=
  if exp = 0 then 1
  else base * power base (exp - 1)

@[reducible, simp]
def solve_precond (n k : Int) : Prop :=
  n > 0 ∧ k ≥ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (h_precond : solve_precond n k) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (result: Int) (h_precond : solve_precond n k) : Prop :=
  result > 0 ∧ result % n = 0 ∧ result % power 10 (Int.natAbs k) = 0 ∧ (∀ m, m > 0 ∧ m % n = 0 ∧ m % power 10 (Int.natAbs k) = 0 → result ≤ m)

theorem solve_spec_satisfied (n k : Int) (h_precond : solve_precond n k) :
    solve_postcond n k (solve n k h_precond) h_precond := by
  sorry
-- </vc-theorems>