-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPowerOfTwo (n: Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_of_two_positive (n : Int) : 
  n ≤ 0 → isPowerOfTwo n = false :=
  sorry

theorem power_of_two_exactly_one_bit {n : Int} :
  n > 0 → (isPowerOfTwo n = true ↔ ∃ k, n = 2^k) :=
  sorry

theorem power_of_two_exp (k : Nat) : 
  isPowerOfTwo (2^k) = true :=
  sorry
-- </vc-theorems>