-- <vc-preamble>
def insertIntoMaxTree (root: Option TreeNode) (val: Int) : TreeNode :=
  sorry

def buildTree (vals: List Int) : Option TreeNode :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def treeToList (t: TreeNode) : List Int :=
  sorry

partial def isMaxTree : TreeNode → Bool 
| TreeNode.node v l r => 
  match l, r with
  | none, none => true 
  | some (TreeNode.node lv ll lr), none => v ≥ lv && isMaxTree (TreeNode.node lv ll lr)
  | none, some (TreeNode.node rv rl rr) => v ≥ rv && isMaxTree (TreeNode.node rv rl rr)
  | some (TreeNode.node lv ll lr), some (TreeNode.node rv rl rr) => 
      v ≥ lv && v ≥ rv && 
      isMaxTree (TreeNode.node lv ll lr) && 
      isMaxTree (TreeNode.node rv rl rr)
-- </vc-definitions>

-- <vc-theorems>
theorem insert_single_node (val: Int) (h: val > 0) : 
  match insertIntoMaxTree none val with
  | TreeNode.node v l r => v = val ∧ l = none ∧ r = none :=
sorry

theorem insert_maintains_values (vals: List Int) (new_val: Int)
  (h1: ∀ x, x ∈ vals → x > 0)
  (h2: new_val > 0) 
  (h3: vals ≠ [])
  (h4: ∀ x y, x ∈ vals → y ∈ vals → x ≠ y) :
  let root := buildTree vals
  let result := insertIntoMaxTree root new_val
  let result_list := treeToList result
  (∀ x, x ∈ vals → x ∈ result_list) ∧ new_val ∈ result_list :=
sorry
-- </vc-theorems>