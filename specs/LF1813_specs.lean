-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_path_sum : TreeNode → Int → List (List Int)
  | _, _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_path_sum_valid_sums (t: TreeNode) (target: Int) :
  ∀ path ∈ find_path_sum t target,
  (path.foldl (· + ·) 0) = target :=
  sorry

theorem empty_tree_no_paths (target: Int) :
  find_path_sum TreeNode.nil target = [] :=
  sorry

theorem single_node_match (val target: Int) :
  find_path_sum (TreeNode.node val TreeNode.nil TreeNode.nil) target =
    if val = target then [[val]] else [] :=
  sorry

/-
info: [[5, 4, 11, 2], [5, 8, 4, 5]]
-/
-- #guard_msgs in
-- #eval find_path_sum TreeNode(5) 22

/-
info: [[1, 2]]
-/
-- #guard_msgs in
-- #eval find_path_sum TreeNode(1) 3

/-
info: []
-/
-- #guard_msgs in
-- #eval find_path_sum None 0
-- </vc-theorems>