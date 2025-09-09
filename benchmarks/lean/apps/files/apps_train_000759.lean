-- <vc-helpers>
-- </vc-helpers>

def reverse_numbers (nums : List String) : List Int := sorry

def is_palindrome (s : String) : Bool := sorry

theorem reverse_numbers_preserves_length {nums : List String} :
  List.length (reverse_numbers nums) = List.length nums := sorry

/-
info: [54321, 30213, 3212, 32]
-/
-- #guard_msgs in
-- #eval reverse_numbers ["12345", "31203", "2123", "2300"]

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval reverse_numbers ["100", "200", "300"]

/-
info: [4321]
-/
-- #guard_msgs in
-- #eval reverse_numbers ["1234"]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible