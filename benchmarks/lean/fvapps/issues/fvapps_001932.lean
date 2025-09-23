-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_adjacent_swaps (n : Nat) (pairs : List Nat) : Nat := sorry

def is_valid_pairs (n : Nat) (pairs : List Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identity_case_requires_zero_swaps (n : Nat) (pairs : List Nat) :
  n > 0 →
  pairs = (List.join (List.map (fun i => [i, i]) (List.range n))) →
  min_adjacent_swaps n pairs = 0 := sorry

theorem worst_case_upper_bound (n : Nat) :
  n > 0 →
  let pairs := List.append (List.range n) (List.range n)
  min_adjacent_swaps n pairs ≤ n * (n-1) / 2 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_adjacent_swaps 4 [1, 1, 2, 3, 3, 2, 4, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_adjacent_swaps 3 [1, 1, 2, 2, 3, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_adjacent_swaps 3 [3, 1, 2, 3, 1, 2]
-- </vc-theorems>