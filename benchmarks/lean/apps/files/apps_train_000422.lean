-- <vc-helpers>
-- </vc-helpers>

def is_possible_divide (nums : List Nat) (k : Nat) : Bool := 
  sorry

theorem list_length_div_k {nums : List Nat} {k : Nat} (h : k > 0) : 
  nums.length % k ≠ 0 → ¬(is_possible_divide nums k) :=
  sorry

theorem single_number_sequence {nums : List Nat} (h : nums.length > 0) :
  is_possible_divide nums 1 :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_possible_divide [1, 2, 3, 3, 4, 4, 5, 6] 4

/-
info: True
-/
-- #guard_msgs in
-- #eval is_possible_divide [3, 2, 1, 2, 3, 4, 3, 4, 5, 9, 10, 11] 3

/-
info: False
-/
-- #guard_msgs in
-- #eval is_possible_divide [1, 2, 3, 4] 3

-- Apps difficulty: interview
-- Assurance level: unguarded