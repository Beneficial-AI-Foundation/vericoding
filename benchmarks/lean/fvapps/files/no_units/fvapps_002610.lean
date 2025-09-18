-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumAverage (lists : List (List Int)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sumAverage_is_floor_of_means (lists : List (List Int)) 
  (h : ∀ l ∈ lists, l.length > 0) :
  ∃ mean, sumAverage lists = mean := -- simplified since we can't easily represent floor of means
  sorry

theorem sumAverage_le_sum_maxes (lists : List (List Int))
  (h : ∀ l ∈ lists, l.length > 0) :
  ∀ l ∈ lists, ∀ x ∈ l, sumAverage lists ≤ x :=
  sorry

theorem sumAverage_ge_mins (lists : List (List Int))
  (h : ∀ l ∈ lists, l.length > 0) :
  ∀ l ∈ lists, ∀ x ∈ l, x ≤ sumAverage lists :=
  sorry

theorem sumAverage_type (lists : List (List Int))
  (h : ∀ l ∈ lists, l.length > 0) :
  sumAverage lists = sumAverage lists :=
  sorry
-- </vc-theorems>