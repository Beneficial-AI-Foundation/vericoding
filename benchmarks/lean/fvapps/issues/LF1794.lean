-- <vc-preamble>
def maxAncestorDiff : Option TreeNode → Int
  | none => 0
  | some _ => sorry

partial def getAllValues : Option TreeNode → List Int
  | none => []
  | some (TreeNode.mk v l r) => v :: (getAllValues l ++ getAllValues r)

def listMaximum (l : List Int) : Int :=
  match l with
  | [] => 0
  | x::xs => List.foldl max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def listMinimum (l : List Int) : Int :=
  match l with
  | [] => 0
  | x::xs => List.foldl min x xs
-- </vc-definitions>

-- <vc-theorems>
theorem maxAncestorDiff_nonnegative (tree : Option TreeNode) :
  maxAncestorDiff tree ≥ 0 := sorry

theorem maxAncestorDiff_single_node (v : Int) :
  maxAncestorDiff (some (TreeNode.mk v none none)) = 0 := sorry

theorem maxAncestorDiff_empty_tree :
  maxAncestorDiff none = 0 := sorry

theorem maxAncestorDiff_bounded (tree : Option TreeNode) :
  tree ≠ none →
  maxAncestorDiff tree ≤ (listMaximum (getAllValues tree) - listMinimum (getAllValues tree)) := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval maxAncestorDiff TreeNode(8)

/-
info: 2
-/
-- #guard_msgs in
-- #eval maxAncestorDiff TreeNode(1)

/-
info: 4
-/
-- #guard_msgs in
-- #eval maxAncestorDiff TreeNode(2)
-- </vc-theorems>