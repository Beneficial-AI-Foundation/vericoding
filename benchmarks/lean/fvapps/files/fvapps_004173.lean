-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def switch_endian (n : Nat) (bits : Nat) : Option Nat := sorry

theorem switch_twice_identity 
  (n : Nat) (bits : Nat) : 
  n < 2^bits → 
  (bits = 8 ∨ bits = 16 ∨ bits = 32) →
  ∀ first_switch, switch_endian n bits = some first_switch → 
  switch_endian first_switch bits = some n := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_inputs_return_none 
  (n : Nat) (bits : Nat) :
  bits < 8 → switch_endian n bits = none := 
sorry

theorem number_too_large_returns_none 
  (n : Nat) (bits : Nat) :
  (bits = 8 ∨ bits = 16 ∨ bits = 32) →
  n ≥ 2^bits → switch_endian n bits = none :=
sorry

theorem eight_bit_numbers_unchanged 
  (n : Nat) :
  n ≤ 255 → 
  switch_endian n 8 = some n :=
sorry

theorem output_in_valid_range 
  (n : Nat) (bits : Nat) (result : Nat) :
  (bits = 8 ∨ bits = 16 ∨ bits = 32) →
  switch_endian n bits = some result → 
  0 ≤ result ∧ result < 2^bits :=
sorry
-- </vc-theorems>