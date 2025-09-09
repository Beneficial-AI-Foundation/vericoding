-- <vc-helpers>
-- </vc-helpers>

def yoga (classroom : List (List Nat)) (poses : List Nat) : Nat := 
  sorry

theorem yoga_nonnegative (classroom : List (List Nat)) (poses : List Nat) :
  yoga classroom poses ≥ 0 := sorry

theorem yoga_empty_inputs (classroom : List (List Nat)) (poses : List Nat) :
  classroom = [] ∨ poses = [] → yoga classroom poses = 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval yoga [[0, 0], [0, 0]] [1, 1, 0, 1, 2, 3, 0, 1, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval yoga [] [1, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval yoga [[0, 0], [0, 0]] []

-- Apps difficulty: introductory
-- Assurance level: guarded