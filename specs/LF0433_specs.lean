-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_teams (rating : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_teams_non_negative (rating : List Int) : 
  num_teams rating ≥ 0 := by sorry

theorem num_teams_short_list {rating : List Int} (h : rating.length < 3) : 
  num_teams rating = 0 := by sorry 

theorem num_teams_symmetric {rating : List Int} (h : rating.length ≥ 3) :
  num_teams rating = num_teams rating.reverse := by sorry

theorem num_teams_strictly_monotone {rating : List Int} (h₁ : rating.length ≥ 3) :
  (∀ i, i < rating.length - 1 → rating[i]! < rating[i+1]!) ∨ 
  (∀ i, i < rating.length - 1 → rating[i]! > rating[i+1]!) →
  num_teams rating = (rating.length * (rating.length - 1) * (rating.length - 2)) / 6 := by sorry

theorem num_teams_all_equal {rating : List Int} (h : rating.length ≥ 3) :
  (∀ x ∈ rating, x = rating[0]!) → 
  num_teams rating = 0 := by sorry
-- </vc-theorems>