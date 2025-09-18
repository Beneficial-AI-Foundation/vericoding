-- <vc-preamble>
def Segment := List Int
def SegmentList := List Segment
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_non_intersecting_segments (segments : SegmentList) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_is_non_negative (segments : SegmentList) :
  count_non_intersecting_segments segments ≥ 0 :=
  sorry

theorem count_less_than_input_size (segments : SegmentList) :
  segments ≠ [] → count_non_intersecting_segments segments ≤ segments.length :=
  sorry 

theorem empty_list_returns_zero :
  count_non_intersecting_segments [] = 0 :=
  sorry

theorem single_segment_returns_one (segment : Segment) :
  segment.length = 2 → count_non_intersecting_segments [segment] = 1 :=
  sorry

theorem identical_segments_count_as_one (segments : SegmentList) (h : segments ≠ []) :
  count_non_intersecting_segments (List.append segments segments) = count_non_intersecting_segments segments :=
  sorry

theorem function_is_deterministic (segments : SegmentList) :
  count_non_intersecting_segments segments = count_non_intersecting_segments segments :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_non_intersecting_segments [[1, 5], [2, 3], [3, 6], [4, 6], [5, 6], [5, 7], [7, 9], [8, 10]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_non_intersecting_segments arr2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded