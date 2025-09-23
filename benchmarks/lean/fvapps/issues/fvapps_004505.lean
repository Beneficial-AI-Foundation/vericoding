-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_bst {α : Type} [Ord α] (values : List α) : Tree α := sorry

def is_bst {α : Type} [Ord α] (t : Tree α) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sorted_values_make_valid_bst {α : Type} [Ord α] (values : List α) :
  is_bst (make_bst values) = true := sorry

theorem empty_tree_is_bst {α : Type} [Ord α] :
  is_bst (Tree.leaf : Tree α) = true := sorry 

theorem single_node_is_bst {α : Type} [Ord α] (x : α) :
  is_bst (Tree.node x Tree.leaf Tree.leaf) = true := sorry

theorem valid_bst_example :
  let t := Tree.node 2 (Tree.node 1 Tree.leaf Tree.leaf) (Tree.node 3 Tree.leaf Tree.leaf)
  is_bst t = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_bst T(5, T(2, T(1), T(3)), T(7, None, T(9)))

/-
info: False
-/
-- #guard_msgs in
-- #eval is_bst T(1, T(2), T(3))

/-
info: True
-/
-- #guard_msgs in
-- #eval is_bst T(7, T(9), T(2))
-- </vc-theorems>