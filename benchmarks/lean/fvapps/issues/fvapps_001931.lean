-- <vc-preamble>
def List.sum [Add α] : List α → α 
  | [] => sorry
  | (x::xs) => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_city_score (n : Nat) (m : Nat) (weights : List Nat) (roads : List (Nat × Nat)) (start : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_city_score_lower_bound (n : Nat) (weights : List Nat) (start : Nat)
  (h1 : n > 0)
  (h2 : weights.length = n) 
  (h3 : start > 0)
  (h4 : start ≤ n) :
  let roads := List.range (n-1) |>.map (λ i => (i+1, i+2))
  let result := max_city_score n (n-1) weights roads start
  result ≥ weights[start-1] := sorry

theorem max_city_score_upper_bound (n : Nat) (weights : List Nat) (start : Nat)
  (h1 : n > 0)
  (h2 : weights.length = n)
  (h3 : start > 0)
  (h4 : start ≤ n) :
  let roads := List.range (n-1) |>.map (λ i => (i+1, i+2))
  let result := max_city_score n (n-1) weights roads start
  result ≤ List.sum weights := sorry

theorem single_city_case (weight : Nat) :
  max_city_score 1 0 [weight] [] 1 = weight := sorry

theorem line_graph_path_sum (n : Nat) (weights : List Nat) (start : Nat)
  (h1 : n ≥ 2)
  (h2 : weights.length = n)
  (h3 : start > 0)
  (h4 : start ≤ n) :
  let roads := List.range (n-1) |>.map (λ i => (i+1, i+2))
  let result := max_city_score n (n-1) weights roads start
  let path_sum := List.sum (List.drop (start-1) weights)
  result ≥ path_sum := sorry

/-
info: 27
-/
-- #guard_msgs in
-- #eval max_city_score 5 7 [2, 2, 8, 6, 9] [(1, 2), (1, 3), (2, 4), (3, 2), (4, 5), (2, 5), (1, 5)] 2

/-
info: 61
-/
-- #guard_msgs in
-- #eval max_city_score 10 12 [1, 7, 1, 9, 3, 3, 6, 30, 1, 10] [(1, 2), (1, 3), (3, 5), (5, 7), (2, 3), (5, 4), (6, 9), (4, 6), (3, 7), (6, 8), (9, 4), (9, 10)] 6

/-
info: 1000000000
-/
-- #guard_msgs in
-- #eval max_city_score 1 0 [1000000000] [] 1
-- </vc-theorems>