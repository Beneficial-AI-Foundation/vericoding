-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def flip_bit (value : Int) (bit_index : Nat) : Int :=
sorry

def band (x y : Int) : Int :=
sorry

def shiftLeft (x : Int) (n : Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem flip_bit_reversible
  (value : Int) (bit_index : Nat)
  (h1 : 1 ≤ bit_index) (h2 : bit_index ≤ 32) :
  flip_bit (flip_bit value bit_index) bit_index = value :=
sorry

theorem flip_bit_changes_target_bit
  (value : Int) (bit_index : Nat)
  (h1 : 1 ≤ bit_index) (h2 : bit_index ≤ 32) :
  ∃ bit_mask : Int,
    bit_mask = shiftLeft 1 (bit_index - 1) ∧
    band value bit_mask ≠ band (flip_bit value bit_index) bit_mask ∧
    band value (bit_mask - 1) = band (flip_bit value bit_index) (bit_mask - 1) :=
sorry
-- </vc-theorems>