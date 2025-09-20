-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_path_binary_tree (i j : Nat) : Nat := sorry

theorem path_to_self {i : Nat} (h : i > 0) : 
  shortest_path_binary_tree i i = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem path_is_symmetric {i j : Nat} (hi : i > 0) (hj : j > 0) :
  shortest_path_binary_tree i j = shortest_path_binary_tree j i := sorry

theorem path_is_nonneg {i j : Nat} (hi : i > 0) (hj : j > 0) :
  shortest_path_binary_tree i j ≥ 0 := sorry 

theorem parent_child_distance {i : Nat} (h : i > 1) :
  shortest_path_binary_tree i (i / 2) = 1 := sorry

theorem triangle_inequality {i j k : Nat} (hi : i > 0) (hj : j > 0) (hk : k > 0) :
  shortest_path_binary_tree i j ≤ shortest_path_binary_tree i k + shortest_path_binary_tree k j := sorry
-- </vc-theorems>