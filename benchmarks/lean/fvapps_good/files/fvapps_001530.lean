-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_triangles_with_incircle (r : Nat) : List (List Nat) := sorry

theorem r1_triangles (r : Nat) :
  r = 1 → find_triangles_with_incircle r = [[3,4,5]] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem r2_triangles (r : Nat) :
  r = 2 → find_triangles_with_incircle r = [[5,12,13], [6,8,10], [6,25,29], [7,15,20], [9,10,17]] := sorry 

theorem zero_radius :
  find_triangles_with_incircle 0 = [] := sorry

theorem result_count_r1 (r : Nat) :
  r = 1 → List.length (find_triangles_with_incircle r) = 1 := sorry

theorem result_count_r2 (r : Nat) :
  r = 2 → List.length (find_triangles_with_incircle r) = 5 := sorry
-- </vc-theorems>