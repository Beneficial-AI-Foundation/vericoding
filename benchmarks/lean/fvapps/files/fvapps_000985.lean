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
-- </vc-theorems>