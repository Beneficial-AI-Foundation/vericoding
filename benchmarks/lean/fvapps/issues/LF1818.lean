-- <vc-preamble>
def arrayToTree (arr : List Int) : Option TreeNode := sorry
def treeToArray (t : TreeNode) : List Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def delNodes (root : Option TreeNode) (to_delete : List Int) : List TreeNode := sorry

theorem delNodes_no_deleted_values (tree : List Int) (to_delete : List Int) 
  (h : ∀ x ∈ tree, x > 0 ∧ x ≤ 100) : 
  let root := arrayToTree tree
  let result := delNodes root to_delete
  let result_arrays := result.map treeToArray
  let all_vals := result_arrays.join
  ∀ val ∈ all_vals, ¬(val ∈ to_delete) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem delNodes_preserves_nondeleted (tree : List Int) (to_delete : List Int) 
  (h : ∀ x ∈ tree, x > 0 ∧ x ≤ 100) :
  let root := arrayToTree tree
  let result := delNodes root to_delete
  let result_arrays := result.map treeToArray
  let all_vals := result_arrays.join
  let original_vals := tree.filter (fun x => ¬(x ∈ to_delete))
  all_vals.length = original_vals.length ∧
  ∀ x, (x ∈ all_vals ↔ x ∈ original_vals) := sorry

theorem delNodes_valid_roots (tree : List Int) (to_delete : List Int)
  (h : ∀ x ∈ tree, x > 0 ∧ x ≤ 100) :
  let root := arrayToTree tree
  let result := delNodes root to_delete
  ∀ t ∈ result, match t with
    | TreeNode.node val _ _ => ¬(val ∈ to_delete) := sorry

theorem delNodes_empty_deletion (tree : List Int)
  (h : ∀ x ∈ tree, x > 0 ∧ x ≤ 100) :
  let root := arrayToTree tree
  let result := delNodes root []
  result.length = 1 ∧ 
  match result with
  | [t] => treeToArray t = tree
  | _ => false := sorry

theorem delNodes_empty_tree :
  delNodes none [1] = [] := sorry

theorem delNodes_single_node :
  let root := some (TreeNode.node 1 none none)
  delNodes root [] = [TreeNode.node 1 none none] ∧
  delNodes root [1] = [] := sorry

/-
info: sorted(map(str, [[1, 2, None, 4], [6], [7]]))
-/
-- #guard_msgs in
-- #eval sorted map(str, result1_arrays)

/-
info: sorted(map(str, [[1, None, 3]]))
-/
-- #guard_msgs in
-- #eval sorted map(str, result2_arrays)
-- </vc-theorems>