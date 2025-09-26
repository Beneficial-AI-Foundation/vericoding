-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kthSmallest (root : TreeNode) (k : Nat) : Int := sorry

def getSortedValues (root : TreeNode) : List Int := sorry

-- Main theorem for kth smallest element matching sorted list
-- </vc-definitions>

-- <vc-theorems>
theorem kth_smallest_matches_sorted
  {root : TreeNode} {vals : List Int} {k : Nat}
  (h1 : k > 0)
  (h2 : k ≤ vals.length)
  (h3 : vals = getSortedValues root) :
  kthSmallest root k = vals[k-1] := sorry

-- Theorem for sorted property of values

theorem sorted_values_ordered
  {root : TreeNode} {vals : List Int}
  (h : vals = getSortedValues root)
  {i : Nat} (hi : i < vals.length - 1) :
  vals[i] ≤ vals[i+1] := sorry

-- Edge case theorems

theorem single_node_kth_smallest
  {n : Int} (root : TreeNode)
  (h1 : root = TreeNode.mk n none none) :
  kthSmallest root 1 = n := sorry

theorem linear_left_tree_first_element
  (root : TreeNode)
  (h1 : root = TreeNode.mk 3 (some (TreeNode.mk 2 (some (TreeNode.mk 1 none none)) none)) none) :
  kthSmallest root 1 = 1 := sorry

theorem linear_right_tree_last_element
  (root : TreeNode)
  (h1 : root = TreeNode.mk 1 none (some (TreeNode.mk 2 none (some (TreeNode.mk 3 none none))))) :
  kthSmallest root 3 = 3 := sorry
-- </vc-theorems>