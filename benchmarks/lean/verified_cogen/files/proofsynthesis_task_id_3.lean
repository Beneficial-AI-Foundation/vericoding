-- <vc-preamble>
-- Specification function for divisibility check
def isDivisible (n : Int) (divisor : Int) : Bool :=
  n % divisor = 0

-- Precondition for isNonPrime
@[reducible, simp]
def isNonPrime_precond (n : Nat) : Prop :=
  n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isNonPrime (n : Nat) (h_precond : isNonPrime_precond n) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isNonPrime_postcond (n : Nat) (result : Bool) (h_precond : isNonPrime_precond n) : Prop :=
  (∃ k : Int, 2 ≤ k ∧ k < n ∧ isDivisible (n : Int) k) ↔ result

theorem isNonPrime_spec_satisfied (n : Nat) (h_precond : isNonPrime_precond n) :
    isNonPrime_postcond n (isNonPrime n h_precond) h_precond := by
  sorry
-- </vc-theorems>