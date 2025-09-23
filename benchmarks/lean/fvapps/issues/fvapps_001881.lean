-- <vc-preamble>
def TreeNode.val : TreeNode → Nat
  | mk v _ _ => v

def print_tree : Option TreeNode → List (List String)
  | none => []
  | some _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_tree_height : Option TreeNode → Nat → Nat
  | none, _ => 0
  | some _, _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem print_tree_props {t : TreeNode} :
  let result := print_tree (some t)
  -- Result is non-empty list of lists
  (result.length > 0) ∧
  -- All rows have same width
  (∀ row ∈ result, row.length = result.head!.length) ∧
  -- Width is 2^height - 1
  (result.head!.length = (2^(get_tree_height (some t) 0)) - 1) ∧
  -- Root in middle of first row
  (result.head!.get! (result.head!.length/2) = toString (TreeNode.val t)) ∧
  -- Non-empty spots are digits
  (∀ row ∈ result, ∀ x ∈ row, x ≠ "" → x.all Char.isDigit) := by
  sorry

theorem get_tree_height_props {t : TreeNode} :
  -- Height is positive for non-empty trees
  get_tree_height (some t) 0 > 0 ∧
  -- Height larger than subtrees
  match t with
  | TreeNode.mk _ l r =>
    ((l.map (get_tree_height · 0)).getD 0 < get_tree_height (some t) 0) ∧
    ((r.map (get_tree_height · 0)).getD 0 < get_tree_height (some t) 0) ∧
    (l.isNone ∧ r.isNone → get_tree_height (some t) 0 = 1)
  := by
  sorry

theorem print_empty_tree :
  print_tree none = [] := by
  sorry

/-
info: [['', '1', ''], ['2', '', '']]
-/
-- #guard_msgs in
-- #eval print_tree TreeNode(1)

/-
info: [['', '', '', '1', '', '', ''], ['', '2', '', '', '', '3', ''], ['', '', '4', '', '', '', '']]
-/
-- #guard_msgs in
-- #eval print_tree TreeNode(1)
-- </vc-theorems>