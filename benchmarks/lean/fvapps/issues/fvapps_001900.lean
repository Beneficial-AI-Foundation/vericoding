-- <vc-preamble>
def buildTree (preorder : List Int) (inorder : List Int) : Option TreeNode :=
  sorry

def inorder_traversal (tree : Option TreeNode) : List Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def preorder_traversal (tree : Option TreeNode) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem buildTree_reconstructs_traversals {size : Nat} (preorder inorder : List Int) :
  (preorder.length = size) →
  (inorder.length = size) →
  size > 0 →
  let tree := buildTree preorder inorder
  inorder_traversal tree = inorder ∧ 
  preorder_traversal tree = preorder :=
sorry

theorem empty_input_gives_none :
  buildTree [] [] = none :=
sorry

theorem single_node_preserves_value (x : Int) :
  let tree := buildTree [x] [x]
  match tree with
  | some (TreeNode.node val left right) => val = x ∧ left = none ∧ right = none 
  | none => False
:=
sorry

/-
info: inorder1
-/
-- #guard_msgs in
-- #eval inorder_traversal buildTree(preorder1, inorder1)

/-
info: preorder1
-/
-- #guard_msgs in
-- #eval preorder_traversal result1

/-
info: inorder2
-/
-- #guard_msgs in
-- #eval inorder_traversal buildTree(preorder2, inorder2)

/-
info: preorder2
-/
-- #guard_msgs in
-- #eval preorder_traversal result2

/-
info: inorder3
-/
-- #guard_msgs in
-- #eval inorder_traversal buildTree(preorder3, inorder3)

/-
info: preorder3
-/
-- #guard_msgs in
-- #eval preorder_traversal result3
-- </vc-theorems>