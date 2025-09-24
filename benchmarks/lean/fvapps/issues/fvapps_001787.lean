-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def vertical_traverse : Option TreeNode → List (List Int)
  | none => []
  | some _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vertical_traverse_type_preservation (t : Option TreeNode) :
  ∀ l ∈ vertical_traverse t, l.all (λ x => True) := by sorry

theorem vertical_traverse_elements_integers (t : Option TreeNode) :
  ∀ l ∈ vertical_traverse t, ∀ x ∈ l, True := by sorry

theorem vertical_traverse_empty (t : Option TreeNode) :
  t = none → vertical_traverse t = [] := by sorry

theorem vertical_traverse_single_node (v : Int) :
  vertical_traverse (some (TreeNode.mk v none none)) = [[v]] := by sorry

theorem vertical_traverse_left_linear (v1 v2 v3 : Int) :
  let t3 := TreeNode.mk v3 none none
  let t2 := TreeNode.mk v2 (some t3) none
  let t1 := TreeNode.mk v1 (some t2) none
  vertical_traverse (some t1) = [[v3], [v2], [v1]] := by sorry

theorem vertical_traverse_right_linear (v1 v2 v3 : Int) :
  let t3 := TreeNode.mk v3 none none
  let t2 := TreeNode.mk v2 none (some t3)
  let t1 := TreeNode.mk v1 none (some t2)
  vertical_traverse (some t1) = [[v1], [v2], [v3]] := by sorry

/-
info: [[9], [3, 15], [20], [7]]
-/
-- #guard_msgs in
-- #eval vertical_traverse TreeNode(3)

/-
info: [[4], [2], [1, 5, 6], [3], [7]]
-/
-- #guard_msgs in
-- #eval vertical_traverse TreeNode(1)
-- </vc-theorems>