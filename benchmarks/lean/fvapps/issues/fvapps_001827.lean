-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def buildCompleteTree {α : Type} (values : List α) : BTree α := sorry

def countCompleteTreeNodes {α : Type} (t : BTree α) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_matches_input_size {α : Type} (values : List α) :
  countCompleteTreeNodes (buildCompleteTree values) = values.length := sorry

theorem perfect_tree_size (h : Nat) : 
  let t : BTree Nat := if h = 0 then BTree.leaf else buildCompleteTree (List.range (2^h - 1))
  countCompleteTreeNodes t = if h = 0 then 0 else 2^h - 1 := sorry

theorem empty_tree_count {α : Type} :
  countCompleteTreeNodes (BTree.leaf : BTree α) = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_complete_tree_nodes TreeNode(1)

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_complete_tree_nodes TreeNode(1)

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_complete_tree_nodes TreeNode(1)
-- </vc-theorems>