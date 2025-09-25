-- <vc-preamble>
def make_tree (values : List Int) (max_depth : Nat := 4) : TreeNode := sorry

def initFindElements (root : TreeNode) : FindElements := {
  root := root,
  find := fun _ => false
}
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isNode : TreeNode → Prop
  | TreeNode.node _ _ _ => True
  | _ => False
-- </vc-definitions>

-- <vc-theorems>
theorem initialization_valid {values : List Int} 
  (h : values.length > 0) (h2 : values.length ≤ 15) :
  let root := make_tree values
  ∃ fe : FindElements, True := sorry

theorem empty_tree_find {target : Int}
  (h : target ≥ 0) (h2 : target ≤ 100) :
  let fe := initFindElements TreeNode.nil
  fe.find target = false := sorry

theorem negative_values_not_found {target : Int}
  (h : target < 0) (h2 : target ≥ -100) :
  let root := make_tree [-1, -1, -1, -1]
  let fe := initFindElements root
  fe.find target = false := sorry

theorem valid_indices_found {values : List Int}
  (h : values.length > 0) (h2 : values.length ≤ 15) :
  let root := make_tree values
  let fe := initFindElements root
  fe.find 0 = true ∧ 
  (isNode root → fe.find 2 = true) ∧
  (isNode root → fe.find 1 = true) := sorry
-- </vc-theorems>