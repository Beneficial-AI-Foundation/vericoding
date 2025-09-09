-- <vc-helpers>
-- </vc-helpers>

def Interval := Int × Int

def eraseOverlapIntervals (intervals : List Interval) : Nat :=
  sorry

theorem eraseOverlapIntervals_output_bounds
  (intervals : List Interval)
  (h : ∀ i ∈ intervals, i.1 ≤ i.2) :
  0 ≤ eraseOverlapIntervals intervals ∧ eraseOverlapIntervals intervals ≤ intervals.length :=
  sorry

theorem eraseOverlapIntervals_empty_list :
  eraseOverlapIntervals [] = 0 :=
  sorry

theorem eraseOverlapIntervals_single_interval
  (i : Interval)
  (h : i.1 ≤ i.2) :
  eraseOverlapIntervals [i] = 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval eraseOverlapIntervals [[1, 2], [2, 3], [3, 4], [1, 3]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval eraseOverlapIntervals [[1, 2], [1, 2], [1, 2]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval eraseOverlapIntervals [[1, 2], [2, 3]]

-- Apps difficulty: interview
-- Assurance level: unguarded