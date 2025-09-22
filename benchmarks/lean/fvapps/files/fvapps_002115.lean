-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_rabbit_hops (n : Nat) (x : Nat) (favorite_nums : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_hops_needed (n : Nat) (x : Nat) (favorite_nums : List Nat)
  (h1 : n > 0) (h2 : x > 0) (h3 : favorite_nums.length > 0) :
  solve_rabbit_hops n x favorite_nums ≥ 1 := by
  sorry

theorem exact_hop_returns_one (n : Nat) (favorite_nums : List Nat) (x : Nat) 
  (h1 : n > 0) (h2 : favorite_nums.length > 0) (h3 : x ∈ favorite_nums) :
  solve_rabbit_hops n x favorite_nums = 1 := by
  sorry

theorem minimum_hops_property (n : Nat) (x : Nat) (favorite_nums : List Nat)
  (h1 : n > 0) (h2 : x > 0) (h3 : favorite_nums.length > 0) (h4 : x ∉ favorite_nums) :
  solve_rabbit_hops n x favorite_nums ≥ 2 := by
  sorry
-- </vc-theorems>