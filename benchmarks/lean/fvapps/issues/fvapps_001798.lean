-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_tree (values : List Int) : TreeNode := sorry

def find_frequent_tree_sum (root : TreeNode) : List Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_frequent_sum_properties 
  (values : List Int) 
  (result := find_frequent_tree_sum (make_tree values)) : 
  -- Empty tree returns empty list
  (values = [] → result = []) ∧
  -- Result is list of integers (satisfied by type system)
  -- All frequencies are equal
  (result ≠ [] → 
    ∀ x y, x ∈ result → y ∈ result → 
    (List.count x result) = (List.count y result))
  := sorry

theorem single_node_tree_property
  (value : Int)
  (root := TreeNode.node value TreeNode.none TreeNode.none) :
  find_frequent_tree_sum root = [value] := sorry

theorem empty_tree_property :
  find_frequent_tree_sum TreeNode.none = [] := sorry

/-
info: [2]
-/
-- #guard_msgs in
-- #eval find_frequent_tree_sum TreeNode(5)

/-
info: []
-/
-- #guard_msgs in
-- #eval find_frequent_tree_sum None
-- </vc-theorems>