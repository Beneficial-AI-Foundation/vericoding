-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def busy_student (startTime : List Int) (endTime : List Int) (queryTime : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem busy_student_empty_lists :
  busy_student [] [] 5 = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval busy_student [1, 2, 3] [3, 2, 7] 4

/-
info: 1
-/
-- #guard_msgs in
-- #eval busy_student [4] [4] 4

/-
info: 0
-/
-- #guard_msgs in
-- #eval busy_student [1, 1, 1, 1] [1, 3, 2, 4] 7
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible