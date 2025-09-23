-- <vc-preamble>
def smallestFromLeaf : TreeNode → String := sorry

theorem smallestFromLeaf_returns_nonempty (root : TreeNode) :
  let result := smallestFromLeaf root
  result.length > 0 := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isTreeOfSize : TreeNode → Nat → Prop 
  | TreeNode.mk _ none none, n => n = 1
  | TreeNode.mk _ (some l) none, n => ∃ m, isTreeOfSize l m ∧ n = m + 1
  | TreeNode.mk _ none (some r), n => ∃ m, isTreeOfSize r m ∧ n = m + 1
  | TreeNode.mk _ (some l) (some r), n => 
    ∃ m₁ m₂, isTreeOfSize l m₁ ∧ isTreeOfSize r m₂ ∧ n = m₁ + m₂ + 1
-- </vc-definitions>

-- <vc-theorems>
theorem smallestFromLeaf_returns_lowercase_chars (root : TreeNode) :
  let result := smallestFromLeaf root
  ∀ c ∈ result.data, 'a' ≤ c ∧ c ≤ 'z' := sorry

theorem smallestFromLeaf_length_bounded_by_tree_size (root : TreeNode) (size : Nat) :
  let result := smallestFromLeaf root
  isTreeOfSize root size → result.length ≤ size := sorry

theorem single_node_returns_a :
  let root := TreeNode.mk 0 none none
  smallestFromLeaf root = "a" := sorry

theorem equal_children_equal_result :
  let root := TreeNode.mk 0 (some (TreeNode.mk 1 none none)) (some (TreeNode.mk 1 none none))
  smallestFromLeaf root = "ba" := sorry

/-
info: 'dba'
-/
-- #guard_msgs in
-- #eval smallestFromLeaf TreeNode(0)

/-
info: 'adz'
-/
-- #guard_msgs in
-- #eval smallestFromLeaf TreeNode(25)

/-
info: 'abc'
-/
-- #guard_msgs in
-- #eval smallestFromLeaf TreeNode(2)
-- </vc-theorems>