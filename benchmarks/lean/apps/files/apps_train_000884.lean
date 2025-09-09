-- <vc-helpers>
-- </vc-helpers>

def can_arrange_students (n : Nat) (boys : List Nat) (girls : List Nat) : String := sorry

theorem can_arrange_students_valid_output (n : Nat) (boys : List Nat) (girls : List Nat) 
  (h1 : n > 0)
  (h2 : boys.length > 0)
  (h3 : girls.length > 0) :
  (can_arrange_students n boys girls = "YES") ∨ 
  (can_arrange_students n boys girls = "NO") := sorry

theorem can_arrange_students_preserves_input_lengths (n : Nat) (boys girls : List Nat)
  (h1 : n > 0)
  (h2 : boys.length = n)
  (h3 : girls.length = n) :
  boys.length = n ∧ girls.length = n := sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_arrange_students 2 [1, 3] [2, 4]

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_arrange_students 3 [5, 3, 8] [2, 4, 6]

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_arrange_students 2 [4, 5] [1, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded