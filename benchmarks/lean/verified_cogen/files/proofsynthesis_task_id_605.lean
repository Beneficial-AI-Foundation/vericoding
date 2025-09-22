-- <vc-preamble>
@[reducible, simp]
def isDivisible (n : Int) (divisor : Int) : Bool :=
  n % divisor = 0

@[reducible, simp]
def primeNum_precond (n : Nat) : Prop :=
  n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def primeNum (n : Nat) (h_precond : primeNum_precond (n)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def primeNum_postcond (n : Nat) (result: Bool) (h_precond : primeNum_precond (n)) :=
  (∀ k : Int, 2 ≤ k → k < n → ¬isDivisible (n : Int) k) ↔ result

theorem primeNum_spec_satisfied (n: Nat) (h_precond : primeNum_precond (n)) :
    primeNum_postcond (n) (primeNum (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>