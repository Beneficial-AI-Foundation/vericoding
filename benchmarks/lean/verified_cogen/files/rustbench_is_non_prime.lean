-- <vc-preamble>
@[reducible, simp]
def isNonPrime_precond (n : Nat) : Prop :=
  n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isNonPrime (n : Nat) (h_precond : isNonPrime_precond (n)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isNonPrime_postcond (n : Nat) (result: Bool) (h_precond : isNonPrime_precond (n)) : Prop :=
  result = true ↔ ∃ k : Int, 2 ≤ k ∧ k < n ∧ (n : Int) % k = 0

theorem isNonPrime_spec_satisfied (n: Nat) (h_precond : isNonPrime_precond (n)) :
    isNonPrime_postcond (n) (isNonPrime (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>