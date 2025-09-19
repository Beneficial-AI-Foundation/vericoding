-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_photo_area (n : Nat) (coords : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_coordinates (n : Nat) (h : 0 < n) (h2 : n ≤ 100) : 
  min_photo_area n (List.replicate (2*n) 0) = 0 := by
  sorry

theorem repeated_value (n : Nat) (val : Int) (h : 0 < n) (h2 : n ≤ 10) (h3 : -100 ≤ val) (h4 : val ≤ 100) :
  min_photo_area n (List.replicate (2*n) val) = 0 := by
  sorry

theorem edge_cases_1 :
  min_photo_area 1 [1,1] = 0 := by
  sorry

theorem edge_cases_2 :
  min_photo_area 2 [1,2,1,2] = 0 := by
  sorry

theorem edge_cases_3 :
  min_photo_area 3 [5,8,5,5,7,5] = 0 := by
  sorry

theorem edge_cases_4 :
  min_photo_area 4 [4,1,3,2,3,2,1,3] = 1 := by
  sorry

theorem ascending_coords (n : Nat) (h : 0 < n) (h2 : n ≤ 10) :
  min_photo_area n (List.map Int.ofNat (List.range (2*n))) ≥ 0 := by
  sorry
-- </vc-theorems>