-- <vc-helpers>
-- </vc-helpers>

def find_largest_nice_number (n: Nat) : Nat := sorry

theorem output_is_natural (n: Nat) (h: n > 0) :
  find_largest_nice_number n ≥ 0 := by sorry

theorem output_le_input (n: Nat) (h: n > 0) : 
  find_largest_nice_number n ≤ n := by sorry

theorem output_is_valid_number (n: Nat) (h: n > 0) :
  let res := toString (find_largest_nice_number n)
  res.length > 0 ∧ 
  res.get 0 ≠ '0' ∧
  res.data.all (fun c => c.isDigit)
  := by sorry

/-
info: 129
-/
-- #guard_msgs in
-- #eval find_largest_nice_number 132

/-
info: 999
-/
-- #guard_msgs in
-- #eval find_largest_nice_number 999

/-
info: 499
-/
-- #guard_msgs in
-- #eval find_largest_nice_number 543

-- Apps difficulty: interview
-- Assurance level: unguarded