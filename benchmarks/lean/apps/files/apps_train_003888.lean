-- <vc-preamble>
def flip_bit (value : Int) (bit_index : Nat) : Int := sorry

def band (x y : Int) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shiftLeft (x : Int) (n : Nat) : Int := sorry

-- States that flipping a bit twice returns the original value
-- </vc-definitions>

-- <vc-theorems>
theorem flip_bit_reversible 
  (value : Int) (bit_index : Nat) 
  (h1 : 1 ≤ bit_index) (h2 : bit_index ≤ 32) :
  flip_bit (flip_bit value bit_index) bit_index = value := sorry

-- States that only the target bit changes

theorem flip_bit_changes_target_bit 
  (value : Int) (bit_index : Nat)
  (h1 : 1 ≤ bit_index) (h2 : bit_index ≤ 32) :
  ∃ bit_mask : Int, 
    bit_mask = shiftLeft 1 (bit_index - 1) ∧
    band value bit_mask ≠ band (flip_bit value bit_index) bit_mask ∧
    band value (bit_mask - 1) = band (flip_bit value bit_index) (bit_mask - 1) := sorry

/-
info: 32768
-/
-- #guard_msgs in
-- #eval flip_bit 0 16

/-
info: 1073741823
-/
-- #guard_msgs in
-- #eval flip_bit 2147483647 31

/-
info: 255
-/
-- #guard_msgs in
-- #eval flip_bit 127 8
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded