-- <vc-preamble>
def isPowerOfTwo (n : Nat) : Prop :=
  n > 0 ∧ ∃ k, n = 2^k
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countOnes (n : Nat) : Nat := sorry

def count_bits (n : Nat) : Array Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_bits_length (n : Nat) (h : n ≤ 1000) :
  (count_bits n).size = n + 1 :=
sorry

theorem count_bits_value (n : Nat) (h : n ≤ 1000) (i : Nat) (h2 : i ≤ n)
  (h3 : i < (count_bits n).size) :
  (count_bits n)[i]'h3 = countOnes i :=
sorry

theorem count_bits_power_of_two (n : Nat) (h : n ≤ 1000) (i : Nat) (h2 : i ≤ n)
  (h3 : i < (count_bits n).size) :
  i > 0 → isPowerOfTwo i → (count_bits n)[i]'h3 = 1 :=
sorry
-- </vc-theorems>