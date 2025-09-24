-- <vc-preamble>
def goodNodes : TreeNode → Nat
  | _ => sorry

def isLinearLeft : TreeNode → List Int → Prop
  | _ , _ => sorry

def countMaxSoFar : List Int → Nat
  | _ => sorry 

def numberOfNodes : TreeNode → Nat 
  | _ => sorry

def allNodesHaveValue : TreeNode → Int → Prop
  | _, _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isStrictlyDecreasing : TreeNode → Prop
  | _ => sorry

/- In a linear tree (only left children), number of good nodes equals number of values 
    that are greater than or equal to all previous values -/
-- </vc-definitions>

-- <vc-theorems>
theorem goodNodes_linear_tree (tree : TreeNode) (path : List Int) :
  isLinearLeft tree path →
  goodNodes tree = countMaxSoFar path := sorry

/- The number of good nodes is always at least 1 (root is always good) -/

theorem goodNodes_at_least_one (tree : TreeNode) :
  goodNodes tree ≥ 1 := sorry 

/- The number of good nodes never exceeds total number of nodes -/

theorem goodNodes_upper_bound (tree : TreeNode) (size : Nat) :
  numberOfNodes tree = size →
  goodNodes tree ≤ size := sorry

/- A single node tree has exactly one good node -/

theorem goodNodes_single_node (val : Int) :
  goodNodes (TreeNode.mk val none none) = 1 := sorry

/- A tree with all same values has all nodes as good nodes -/

theorem goodNodes_all_same_value (val : Int) (tree : TreeNode) :
  allNodesHaveValue tree val →
  goodNodes tree = numberOfNodes tree := sorry

/- A strictly decreasing tree has exactly one good node -/

theorem goodNodes_strictly_decreasing (tree : TreeNode) :
  isStrictlyDecreasing tree →
  goodNodes tree = 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval goodNodes TreeNode(3)

/-
info: 3
-/
-- #guard_msgs in
-- #eval goodNodes TreeNode(3)

/-
info: 1
-/
-- #guard_msgs in
-- #eval goodNodes TreeNode(1)
-- </vc-theorems>