-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def zigzagLevelOrder (root : Option TreeNode) : List (List Int) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zigzagLevelOrder_valid {root : Option TreeNode} :
  let result := zigzagLevelOrder root
  -- Result is a list of lists
  result.all (fun level => level.all (fun x => x ≥ -100 ∧ x ≤ 100)) ∧
  -- Each level length is at most double the previous
  result.tail.all (fun level => 
    match result.head? with
    | some prev => level.length ≤ 2 * prev.length 
    | none => true) :=
  sorry

theorem zigzagLevelOrder_empty :
  zigzagLevelOrder none = [] :=
  sorry

theorem zigzagLevelOrder_single_node :
  zigzagLevelOrder (some (TreeNode.node 1 none none)) = [[1]] := 
  sorry

/-
info: [[3], [20, 9], [15, 7]]
-/
-- #guard_msgs in
-- #eval zigzagLevelOrder TreeNode(3)

/-
info: [[1]]
-/
-- #guard_msgs in
-- #eval zigzagLevelOrder TreeNode(1)

/-
info: []
-/
-- #guard_msgs in
-- #eval zigzagLevelOrder None
-- </vc-theorems>