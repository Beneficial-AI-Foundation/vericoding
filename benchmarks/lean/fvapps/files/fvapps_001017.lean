-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_square_intersection (a k x1 x2 x3 : Float) : Float := sorry

theorem intersection_bounds 
  (a k x1 x2 x3 : Float)
  (ha : 0.1 ≤ a ∧ a ≤ 1000)
  (hk : 0 ≤ k ∧ k ≤ 1000)
  (hx1 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (hx2 : -1000 ≤ x2 ∧ x2 ≤ 1000) 
  (hx3 : -1000 ≤ x3 ∧ x3 ≤ 1000) :
  let result := calculate_square_intersection a k x1 x2 x3
  0 ≤ result ∧ result ≤ a * a :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem large_k_zero_intersection
  (a k x1 x2 x3 : Float)
  (ha : 0.1 ≤ a ∧ a ≤ 1000)
  (hk : 0 ≤ k ∧ k ≤ 1000)
  (hx1 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (hx2 : -1000 ≤ x2 ∧ x2 ≤ 1000)
  (hx3 : -1000 ≤ x3 ∧ x3 ≤ 1000)
  (h_dist : max x1 (max x2 x3) - min x1 (min x2 x3) - 2*k ≥ a) :
  calculate_square_intersection a k x1 x2 x3 = 0 :=
sorry

theorem small_k_full_intersection
  (a k x1 x2 x3 : Float)
  (ha : 0.1 ≤ a ∧ a ≤ 1000)
  (hk : 0 ≤ k ∧ k ≤ 1000)
  (hx1 : -1000 ≤ x1 ∧ x1 ≤ 1000)
  (hx2 : -1000 ≤ x2 ∧ x2 ≤ 1000)
  (hx3 : -1000 ≤ x3 ∧ x3 ≤ 1000)
  (h_dist : max x1 (max x2 x3) - min x1 (min x2 x3) - 2*k ≤ 0) :
  (calculate_square_intersection a k x1 x2 x3 - a*a).abs < 0.001 := 
sorry

theorem same_points_full_intersection
  (a : Float)
  (ha : 0.1 ≤ a ∧ a ≤ 1000) :
  (calculate_square_intersection a 0 1 1 1 - a*a).abs < 0.001 :=
sorry
-- </vc-theorems>