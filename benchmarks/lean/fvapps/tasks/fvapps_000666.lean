-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def assess_lights (k : Nat) (n : Nat) (points : List (Nat × Nat)) : String := sorry

theorem more_than_three_lights_always_yes {n k : Nat} {points : List (Nat × Nat)}
  (h1 : 1 ≤ n) (h2 : n ≤ 100) 
  (h3 : 1 ≤ k) (h4 : k ≤ 4)
  (h5 : k > 3)
  : assess_lights k n points = "yes" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem corner_point_always_yes {n : Nat} {points : List (Nat × Nat)}
  (h1 : 2 ≤ n) (h2 : n ≤ 100)
  (h3 : points.length ≤ 3)
  (h4 : ∃ p ∈ points, p = (0,0) ∨ p = (0,n-1) ∨ p = (n-1,0) ∨ p = (n-1,n-1))
  : assess_lights points.length n points = "yes" := sorry

theorem two_edge_points_yes {n : Nat}
  (h1 : 2 ≤ n) (h2 : n ≤ 100) :
  (assess_lights 2 n [(0,1), (0,n-2)] = "yes") ∧ 
  (assess_lights 2 n [(1,0), (n-2,0)] = "yes") := sorry

theorem three_points_valid_result {n x y : Nat}
  (h1 : 2 ≤ n) (h2 : n ≤ 100)
  (h3 : x ≤ 99) (h4 : y ≤ 99) :
  (assess_lights 3 n [(0,0), (x % n, y % n), (n-1,n-1)] = "yes") ∨
  (assess_lights 3 n [(0,0), (x % n, y % n), (n-1,n-1)] = "no") := sorry
-- </vc-theorems>