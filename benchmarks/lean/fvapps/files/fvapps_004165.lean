-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def next_higher (n : Nat) : Nat :=
  sorry

def countOnes (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem next_higher_preserves_bit_count (n : Nat) (h : n > 0) (h2 : n < 2^16) :
  countOnes n = countOnes (next_higher n) :=
sorry

theorem next_higher_is_higher (n : Nat) (h : n > 0) (h2 : n < 2^16) :
  next_higher n > n :=
sorry

theorem next_higher_power_two (i : Nat) (h : i < 8) :
  next_higher (2^i) = 2^(i+1) :=
sorry
-- </vc-theorems>