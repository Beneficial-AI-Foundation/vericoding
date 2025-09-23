-- <vc-preamble>
def maxDepth {α : Type} : Tree α → Nat
  | Tree.leaf => 0
  | Tree.node _ l r => max (maxDepth l) (maxDepth r) + 1

def getDeepestNodes {α : Type} : Tree α → Nat → List (Tree α)
  | _, _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def subtreeWithAllDeepest {α : Type} : Tree α → Tree α
  | t => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_none {α : Type} (t : Tree α) :
  subtreeWithAllDeepest t ≠ Tree.leaf := sorry

theorem deepest_nodes_preserved {α : Type} (t : Tree α) : 
  let result := subtreeWithAllDeepest t
  let maxDepthTree := maxDepth t
  let maxDepthResult := maxDepth result
  let deepestNodesTree := getDeepestNodes t maxDepthTree
  let deepestNodesResult := getDeepestNodes result maxDepthResult
  deepestNodesTree = deepestNodesResult := sorry

theorem smallest_possible_subtree {α : Type} (t : Tree α) :
  let result := subtreeWithAllDeepest t
  match result with
  | Tree.leaf => True
  | Tree.node _ l r => 
    let leftDepth := maxDepth l
    let rightDepth := maxDepth r
    leftDepth = rightDepth ∨ (leftDepth ≤ rightDepth + 1 ∧ rightDepth ≤ leftDepth + 1) := sorry

theorem single_node_case {α : Type} (x : α) :
  subtreeWithAllDeepest (Tree.node x Tree.leaf Tree.leaf) = Tree.node x Tree.leaf Tree.leaf := sorry
-- </vc-theorems>