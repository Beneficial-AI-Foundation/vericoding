-- <vc-preamble>
def sumOfDigits (n : Nat) : Nat :=
  if n = 0 then 0
  else (n % 10) + sumOfDigits (n / 10)
termination_by n

def ValidInput (N : Int) : Prop :=
  N ≥ 1

def IsDivisibleByDigitSum (N : Int) : Prop :=
  N.natAbs % sumOfDigits N.natAbs = 0

@[reducible, simp]
def solve_precond (N : Int) : Prop :=
  ValidInput N
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (N : Int) (h_precond : solve_precond N) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (N : Int) (result : String) (h_precond : solve_precond N) : Prop :=
  (result = "Yes" ∨ result = "No") ∧ (result = "Yes" ↔ IsDivisibleByDigitSum N)

theorem solve_spec_satisfied (N : Int) (h_precond : solve_precond N) :
    solve_postcond N (solve N h_precond) h_precond := by
  sorry
-- </vc-theorems>