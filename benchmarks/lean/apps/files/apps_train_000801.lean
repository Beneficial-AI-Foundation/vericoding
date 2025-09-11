-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Interval := Int × Int

def color_intervals (intervals : List Interval) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem color_intervals_outputs_valid_binary : ∀ (intervals : List Interval),
  let result := color_intervals intervals
  (∀ c ∈ result.data, c = '0' ∨ c = '1') ∧ 
  result.length = intervals.length
  := sorry

theorem non_overlapping_intervals_share_colors : ∀ (intervals : List Interval),
  intervals.length ≥ 2 →
  (∀ i ∈ intervals, i.1 < i.2) →
  let sorted := intervals 
  (∀ (i : Interval), ∀ (j : Interval), i ∈ sorted → j ∈ sorted → i.2 < j.1 ∨ j.2 < i.1) →
  let result := color_intervals intervals
  2 ≥ List.length (List.eraseDups result.data)
  := sorry

/-
info: '100'
-/
-- #guard_msgs in
-- #eval color_intervals [(3, 7), (2, 5), (6, 9)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded