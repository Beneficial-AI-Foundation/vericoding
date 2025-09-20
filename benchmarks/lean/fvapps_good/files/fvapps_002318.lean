-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_alternating_bits (n : Nat) : Bool := sorry

def binary_to_list (n : Nat) : List Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem alternating_bits_adjacent_different (n : Nat) :
  has_alternating_bits n = true →
  ∀ bits, bits = binary_to_list n →
  ∀ i h₁ h₂, i < bits.length - 1 →
  bits[i]'h₁ ≠ bits[i+1]'h₂ := sorry

theorem alternating_bits_balanced_ones_zeros (n : Nat) :
  has_alternating_bits n = true →
  ∀ bits, bits = binary_to_list n →
  let ones := bits.filter id |>.length;
  let zeros := bits.filter not |>.length;
  ones ≤ zeros + 1 ∧ zeros ≤ ones + 1 := sorry

theorem power_of_two_not_alternating (n : Nat) :
  n > 1 →
  n &&& (n-1) = 0 → 
  has_alternating_bits n = false := sorry

theorem alternating_bits_consistent (n : Nat) :
  let result := has_alternating_bits n
  has_alternating_bits n = result := sorry
-- </vc-theorems>