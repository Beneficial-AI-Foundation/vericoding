-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_all (xs : List Int) (n : Int) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_all_valid_indices {xs : List Int} {n : Int} :
  ∀ i ∈ find_all xs n, i < xs.length := by
  sorry

theorem find_all_ascending {xs : List Int} {n : Int} :
  ∀ i j, i < j → 
  i ∈ find_all xs n → 
  j ∈ find_all xs n → 
  i < j := by
  sorry

theorem find_all_points_to_target {xs : List Int} {n : Int} :
  ∀ i, i ∈ find_all xs n → 
  ∃ h : i < xs.length, xs[i]'h = n := by
  sorry

theorem find_all_complete {xs : List Int} {n : Int} :
  ∀ i, i < xs.length →
  (∃ h : i < xs.length, xs[i]'h = n) →
  i ∈ find_all xs n := by
  sorry

theorem find_all_missing {xs : List Int} {n : Int} :
  (∀ x ∈ xs, x ≠ n) →
  find_all xs n = [] := by
  sorry

theorem find_all_present {xs : List Int} {n : Int} :
  n ∈ xs →
  find_all xs n ≠ [] := by
  sorry
-- </vc-theorems>