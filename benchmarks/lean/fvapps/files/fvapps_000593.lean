-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_social_distancing (n : Nat) (arr : List Nat) : String := sorry

theorem check_social_distancing_returns_valid_result (n : Nat) (arr : List Nat)
  (h1 : n ≥ 2) (h2 : n ≤ 100)
  (h3 : ∀ x ∈ arr, x = 0 ∨ x = 1) :
  check_social_distancing n arr = "YES" ∨ 
  check_social_distancing n arr = "NO" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem check_social_distancing_minimum_distance (n : Nat) (arr : List Nat)
  (h1 : arr.length = n)
  (h2 : ∀ x ∈ arr, x = 0 ∨ x = 1) :
  check_social_distancing n arr = "YES" ↔ 
  (∀ i j, i < arr.length → j < arr.length → i < j → 
   arr[i]! = 1 → arr[j]! = 1 → j - i ≥ 6) := sorry

theorem check_social_distancing_minimum_valid (n : Nat)
  (h1 : n ≥ 7) (h2 : n ≤ 100) :
  let arr := List.replicate n 0
  let arr' := arr.set 0 1
  let arr'' := arr'.set 6 1
  check_social_distancing n arr'' = "YES" := sorry

theorem check_social_distancing_edge_cases :
  (check_social_distancing 1 [0] = "YES") ∧
  (check_social_distancing 1 [1] = "YES") ∧
  (check_social_distancing 2 [1,1] = "NO") := sorry
-- </vc-theorems>