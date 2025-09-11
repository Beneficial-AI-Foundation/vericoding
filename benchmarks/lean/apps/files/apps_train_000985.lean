-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_late_submissions (submissions : List (Nat × Nat)) : Nat := sorry

theorem count_late_submissions_non_negative (submissions : List (Nat × Nat)) :
  count_late_submissions submissions ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_late_submissions_upper_bound (submissions : List (Nat × Nat)) :
  count_late_submissions submissions ≤ submissions.length := sorry

theorem count_late_submissions_manual_count (submissions : List (Nat × Nat)) :
  count_late_submissions submissions = 
    (submissions.filter (fun p => p.2 - p.1 > 5)).length := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_late_submissions [(1, 3), (4, 4), (4, 10), (1, 11), (2, 7)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_late_submissions [(1, 2), (3, 4), (5, 6)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_late_submissions [(1, 7), (2, 8), (3, 9)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible