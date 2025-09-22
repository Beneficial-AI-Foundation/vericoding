-- <vc-preamble>
def SumOfDigits (n : Nat) : Nat :=
  if n < 10 then n
  else (n % 10) + SumOfDigits (n / 10)
termination_by n
decreasing_by simp_wf; simp [Nat.div_lt_iff_lt_mul]; omega

def ValidOutput (result : List Int) (k : Int) : Prop :=
  result.length = k.natAbs ∧
  (∀ i, i < result.length → result[i]! > 0) ∧
  (∀ i, i + 1 < result.length → result[i]! < result[i + 1]!) ∧
  (k ≥ 1 → result.length ≥ 1 ∧ result[0]! = 1) ∧
  (k ≥ 2 → result.length ≥ 2 ∧ result[1]! = 2) ∧
  (k ≥ 3 → result.length ≥ 3 ∧ result[2]! = 3) ∧
  (k ≥ 4 → result.length ≥ 4 ∧ result[3]! = 4) ∧
  (k ≥ 5 → result.length ≥ 5 ∧ result[4]! = 5) ∧
  (k ≥ 6 → result.length ≥ 6 ∧ result[5]! = 6) ∧
  (k ≥ 7 → result.length ≥ 7 ∧ result[6]! = 7) ∧
  (k ≥ 8 → result.length ≥ 8 ∧ result[7]! = 8) ∧
  (k ≥ 9 → result.length ≥ 9 ∧ result[8]! = 9) ∧
  (k ≥ 10 → result.length ≥ 10 ∧ result[9]! = 19)

@[reducible, simp]
def solve_precond (k : Int) : Prop :=
  k ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (k : Int) (h_precond : solve_precond k) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (k : Int) (result : List Int) (h_precond : solve_precond k) : Prop :=
  ValidOutput result k

theorem solve_spec_satisfied (k : Int) (h_precond : solve_precond k) :
    solve_postcond k (solve k h_precond) h_precond := by
  sorry
-- </vc-theorems>