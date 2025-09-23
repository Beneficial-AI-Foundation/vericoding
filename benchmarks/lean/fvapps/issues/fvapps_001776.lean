-- <vc-preamble>
def generateTrees (n : Nat) : List TreeNode :=
  sorry

def tree_to_list (t : TreeNode) : List Nat :=
  sorry

def is_bst_valid (t : TreeNode) (min max : Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def contains_all_values (t : TreeNode) (n : Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generateTrees_empty (n : Nat) :
  n = 0 → generateTrees n = [] :=
  sorry

theorem generate_trees_count_catalan (n : Nat) :
  n ≤ 8 →
  let catalan := [1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862]
  List.length (generateTrees n) = List.get! catalan n :=
  sorry

theorem generate_trees_are_valid_bst (n : Nat) (t : TreeNode) :
  t ∈ generateTrees n →
  is_bst_valid t (-2^31) (2^31 - 1) = true :=
  sorry

theorem generate_trees_contain_all_values (n : Nat) (t : TreeNode) :
  t ∈ generateTrees n →
  contains_all_values t n = true :=
  sorry 

theorem generate_trees_are_unique (n : Nat) :
  let tree_lists := List.map tree_to_list (generateTrees n)
  List.length (List.eraseDups tree_lists) = List.length (generateTrees n) :=
  sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval generateTrees 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval len generateTrees(1)

/-
info: [1]
-/
-- #guard_msgs in
-- #eval tree_to_list trees[0]

/-
info: 5
-/
-- #guard_msgs in
-- #eval len generateTrees(3)
-- </vc-theorems>