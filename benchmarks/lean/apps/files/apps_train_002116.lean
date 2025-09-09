-- <vc-helpers>
-- </vc-helpers>

def find_array_element (n : Nat) (x : Nat) : Nat :=
sorry

theorem find_array_element_in_bounds {n x : Nat} (hn : n > 0) (hx : x > 0) (hxn : x ≤ n) : 
  1 ≤ find_array_element n x ∧ find_array_element n x ≤ n :=
sorry

theorem find_array_element_first {n : Nat} (hn : n > 0) :
  find_array_element n 1 = 1 :=
sorry

theorem find_array_element_bijective {n : Nat} (hn : n > 1) :
  ∀ y : Nat, 1 ≤ y ∧ y ≤ n → ∃ x : Nat, 1 ≤ x ∧ x ≤ n ∧ find_array_element n x = y :=
sorry

/-
info: expected[i]
-/
-- #guard_msgs in
-- #eval find_array_element 4 queries[i]

/-
info: expected[i]
-/
-- #guard_msgs in
-- #eval find_array_element 13 queries[i]

/-
info: expected[i]
-/
-- #guard_msgs in
-- #eval find_array_element 3 queries[i]

-- Apps difficulty: competition
-- Assurance level: unguarded