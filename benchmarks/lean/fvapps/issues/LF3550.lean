-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_time (pairs : List TimePair) : List TimePair :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_time_length_preserving
  (pairs : List TimePair) :
  List.length (sort_time pairs) = List.length pairs :=
  sorry

theorem sort_time_elements_same
  (pairs : List TimePair) :
  ∀ x, x ∈ sort_time pairs ↔ x ∈ pairs :=
  sorry

theorem sort_time_valid_ordering
  (pairs : List TimePair) 
  (i : Nat)
  (h₁ : i < List.length (sort_time pairs) - 1)
  (h₂ : i < List.length (sort_time pairs))
  (h₃ : i + 1 < List.length (sort_time pairs)) :
  let result := sort_time pairs
  let curr := result[i]'h₂
  let next := result[i+1]'h₃
  next.start < curr.end_ → curr.end_ > next.start :=
  sorry

theorem sort_time_idempotent
  (pairs : List TimePair) :
  sort_time (sort_time pairs) = sort_time pairs :=
  sorry

theorem sort_time_concatenation
  (lists : List (List TimePair))
  (h : lists ≠ []) :
  let flattened := List.join lists
  sort_time flattened = sort_time (sort_time flattened) :=
  sorry
-- </vc-theorems>