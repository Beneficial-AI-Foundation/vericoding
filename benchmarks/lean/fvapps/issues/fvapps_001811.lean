-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_bottom_left_value {α : Type} (t : BinaryTree α) : Option α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_path_tree {α : Type} (v₁ v₂ v₃ v₄ v₅ : α) :
  let t := BinaryTree.node v₁
             (BinaryTree.node v₂
               (BinaryTree.node v₃
                 (BinaryTree.node v₄
                   (BinaryTree.node v₅ BinaryTree.leaf BinaryTree.leaf)
                   BinaryTree.leaf)
                 BinaryTree.leaf)
               BinaryTree.leaf)
             BinaryTree.leaf
  find_bottom_left_value t = some v₅ :=
sorry

theorem complete_binary_tree :
  let t := BinaryTree.node 1
             (BinaryTree.node 2
               (BinaryTree.node 4 BinaryTree.leaf BinaryTree.leaf)
               (BinaryTree.node 5 BinaryTree.leaf BinaryTree.leaf))
             (BinaryTree.node 3
               (BinaryTree.node 6 BinaryTree.leaf BinaryTree.leaf)
               (BinaryTree.node 7 BinaryTree.leaf BinaryTree.leaf))
  find_bottom_left_value t = some 4 :=
sorry

theorem single_node_tree {α : Type} (v : α) :
  find_bottom_left_value (BinaryTree.node v BinaryTree.leaf BinaryTree.leaf) = some v :=
sorry

theorem asymmetric_tree :
  let t := BinaryTree.node 1
             (BinaryTree.node 2 BinaryTree.leaf BinaryTree.leaf)
             (BinaryTree.node 3
               (BinaryTree.node 4 BinaryTree.leaf BinaryTree.leaf)
               BinaryTree.leaf)
  find_bottom_left_value t = some 4 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_bottom_left_value TreeNode(2)

/-
info: 7
-/
-- #guard_msgs in
-- #eval find_bottom_left_value TreeNode(1)
-- </vc-theorems>