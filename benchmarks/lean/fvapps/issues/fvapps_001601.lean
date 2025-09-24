-- <vc-preamble>
def treeByLevels {α : Type} (t : BTree α) : List α :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def buildTree {α : Type} (values : List α) : BTree α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_tree_gives_empty_list {α : Type} :
  treeByLevels (BTree.leaf : BTree α) = [] :=
sorry

theorem tree_length {α : Type} (values : List α) (h : values ≠ []) :
  let tree := buildTree values
  List.length (treeByLevels tree) = List.length values :=
sorry

theorem root_is_first {α : Type} [Inhabited α] (values : List α) (h : values ≠ []) (v : α) (vs : List α) 
  (h2 : values = v :: vs) :
  let tree := buildTree values
  List.head? (treeByLevels tree) = some v :=
sorry

theorem values_preserved_length {α : Type} (values : List α) (h : values ≠ []) :
  let tree := buildTree values
  List.length (treeByLevels tree) = List.length values :=
sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval tree_by_levels None

/-
info: [2, 8, 9, 1, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval tree_by_levels Node(Node(Node(None, None, 1), Node(None, None, 3), 8), Node(Node(None, None, 4), Node(None, None, 5), 9), 2)

/-
info: [1, 8, 4, 3, 5, 7]
-/
-- #guard_msgs in
-- #eval tree_by_levels Node(Node(None, Node(None, None, 3), 8), Node(None, Node(None, Node(None, None, 7), 5), 4), 1)
-- </vc-theorems>