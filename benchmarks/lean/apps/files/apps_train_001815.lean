-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def xorGame (nums : List Nat) : Bool := sorry

def xorSum (nums : List Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem xorGame_even_length_true {nums : List Nat} (h : nums.length % 2 = 0) : 
  xorGame nums = true := sorry

theorem xorGame_odd_length {nums : List Nat} (h : nums.length % 2 = 1) :
  xorGame nums = (xorSum nums = 0) := sorry

theorem xorGame_consistent {nums : List Nat} :
  let result := xorGame nums
  ∀ n : Nat, xorGame nums = result := sorry

theorem xorGame_even_length_general {nums : List Nat} :
  nums.length ≥ 2 → nums.length % 2 = 0 → xorGame nums = true := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval xor_game [1, 1, 2]

/-
info: True
-/
-- #guard_msgs in
-- #eval xor_game [0, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval xor_game [1, 2, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded