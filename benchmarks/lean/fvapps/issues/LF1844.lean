-- <vc-preamble>
def bstFromPreorder (preorder : List Int) : TreeNode :=
  sorry

def treeToList (root : TreeNode) : List Int :=
  sorry

def is_valid_bst (preorder : List Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_bst (node : TreeNode) (min_val max_val : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem bst_from_preorder_preserves_values (preorder : List Int) :
  is_valid_bst preorder →
  let result := treeToList (bstFromPreorder preorder)
  (∀ x, x ∈ preorder → x ∈ result) ∧ 
  (∀ x, x ∈ result → x ∈ preorder) :=
  sorry

theorem bst_from_preorder_maintains_bst_property (preorder : List Int) :
  is_valid_bst preorder →
  is_bst (bstFromPreorder preorder) (-1000) 1000 :=
  sorry

theorem bst_from_preorder_structure (preorder : List Int) :
  is_valid_bst preorder →
  treeToList (bstFromPreorder preorder) = treeToList (bstFromPreorder preorder) :=
  sorry

/-
info: [8, 5, 10, 1, 7, None, 12]
-/
-- #guard_msgs in
-- #eval treeToList bstFromPreorder([8, 5, 1, 7, 10, 12])

/-
info: [1]
-/
-- #guard_msgs in
-- #eval treeToList bstFromPreorder([1])

/-
info: [5, 3, 7, 1, 4, 6, 8]
-/
-- #guard_msgs in
-- #eval treeToList bstFromPreorder([5, 3, 1, 4, 7, 6, 8])
-- </vc-theorems>