-- <vc-helpers>
-- </vc-helpers>

def find_lowest_int (k : Nat) : Nat := sorry

def digits_to_sorted_list (n : Nat) : List Nat := sorry

theorem find_lowest_int_positive (k : Nat) (h : k > 0) : 
  find_lowest_int k > 0 := sorry

theorem find_lowest_int_products_different (k : Nat) (h : k > 0) :
  find_lowest_int k * k ≠ find_lowest_int k * (k + 1) := sorry

/-
info: 8919
-/
-- #guard_msgs in
-- #eval find_lowest_int 100

/-
info: 477
-/
-- #guard_msgs in
-- #eval find_lowest_int 325

/-
info: 2394
-/
-- #guard_msgs in
-- #eval find_lowest_int 599

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible