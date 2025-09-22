-- <vc-preamble>
@[reducible]
def ifPowerOfFour_precond (n : Nat) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ifPowerOfFour (n : Nat) (h_precond : ifPowerOfFour_precond (n)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def ifPowerOfFour_postcond (n : Nat) (result: Bool) (h_precond : ifPowerOfFour_precond (n)) : Prop :=
  result ↔ (∃ m:Nat, n=4^m)

theorem ifPowerOfFour_spec_satisfied (n: Nat) (h_precond : ifPowerOfFour_precond (n)) :
    ifPowerOfFour_postcond (n) (ifPowerOfFour (n) h_precond) h_precond := by
  sorry
-- </vc-theorems>