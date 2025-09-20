-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_distance (n k d : Nat) (x : List Nat) (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_distance_basic_bounds 
  {n k d : Nat} {x l : List Nat} 
  (h1 : 0 < n) (h2 : 20 ≤ k) (h3 : 0 < d ∧ d ≤ 10)
  (h4 : x.length = n) (h5 : l.length = n)
  (h6 : ∀ i, i ∈ x → 0 < i ∧ i ≤ 20)
  (h7 : ∀ i, i ∈ l → 0 < i ∧ i ≤ 2)
  (h8 : x.length > 0)
  : x.head! ≤ max_distance n k d x l ∧ max_distance n k d x l ≤ k :=
  sorry

theorem max_distance_single_obstacle
  : max_distance 1 10 1 [5] [1] = 10 :=
  sorry 

theorem max_distance_two_adjacent_obstacles
  : max_distance 2 10 2 [5,6] [1,2] = 6 :=
  sorry
-- </vc-theorems>