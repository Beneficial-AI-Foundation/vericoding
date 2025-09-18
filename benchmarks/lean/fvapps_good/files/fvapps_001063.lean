-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_cake_sharing (n_friends : Nat) (length : Nat) (breadth : Nat) : String := sorry

theorem cake_sharing_remaining_area (n_friends length breadth : Nat)
  (h1 : n_friends > 0) (h2 : length > 0) (h3 : breadth > 0) :
  ∀ n : Nat,
  solve_cake_sharing n_friends length breadth = s!"Yes {n}" →
  n < length * breadth ∧ n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_cake_multiple_friends (size friends : Nat)
  (h1 : size > 0) (h2 : size < 10) (h3 : friends ≥ 2) (h4 : friends < 10) :
  solve_cake_sharing friends size size = "No" := sorry

theorem single_friend_solution (size : Nat)
  (h1 : size > 0) (h2 : size ≤ 100) :
  solve_cake_sharing 1 size (size + 1) = s!"Yes {size}" := sorry

theorem dimension_order_invariant (length breadth : Nat)
  (h1 : length > 0) (h2 : breadth > 0) (h3 : length ≤ 100) (h4 : breadth ≤ 100) :
  solve_cake_sharing 1 length breadth = solve_cake_sharing 1 breadth length := sorry
-- </vc-theorems>