-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hammingWeight (n: Nat) : Nat :=
sorry

def bitLength (n: Nat) : Nat :=
sorry

def isPowerOfTwo (n: Nat) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hamming_weight_nonnegative_and_bounded (x: Nat) :
  hammingWeight x ≥ 0 ∧ hammingWeight x ≤ bitLength x :=
sorry

theorem hamming_weight_power_of_two (x: Nat) :
  x > 0 → isPowerOfTwo x → hammingWeight x = 1 :=
sorry

theorem hamming_weight_zero_and_nonzero (x: Nat) :
  hammingWeight 0 = 0 ∧ (x > 0 → hammingWeight x > 0) :=
sorry
-- </vc-theorems>