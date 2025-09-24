-- <vc-preamble>
def TreeNode.val : TreeNode → Int
  | mk v _ _ => v

def TreeNode.left : TreeNode → Option TreeNode
  | mk _ l _ => l

def TreeNode.right : TreeNode → Option TreeNode
  | mk _ _ r => r

def build_tree_from_list (values : List Int) : Option TreeNode :=
  sorry

def clone_tree (root : Option TreeNode) : Option TreeNode :=
  sorry

def get_leftmost_node (root : Option TreeNode) : Option TreeNode :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getTargetCopy (original cloned target: Option TreeNode) : Option TreeNode :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem target_copy_leftmost_preserves_values
  (values : List Int) (h : values.length > 0)
  (original : Option TreeNode) (h₁ : original = build_tree_from_list values)
  (cloned : Option TreeNode) (h₂ : cloned = clone_tree original)
  (target : Option TreeNode) (h₃ : target = get_leftmost_node original) :
  match getTargetCopy original cloned target with
  | none => False
  | some result => 
    match target with
    | none => False
    | some t =>
      (TreeNode.val result = TreeNode.val t) ∧
      (Option.isSome (TreeNode.left t) → 
        Option.isSome (TreeNode.left result) ∧
        (∀ rl tl, TreeNode.left result = some rl → TreeNode.left t = some tl → 
          TreeNode.val rl = TreeNode.val tl)) ∧
      (Option.isSome (TreeNode.right t) →
        Option.isSome (TreeNode.right result) ∧
        (∀ rr tr, TreeNode.right result = some rr → TreeNode.right t = some tr → 
          TreeNode.val rr = TreeNode.val tr))
  :=
  sorry

theorem target_copy_root_preserves_values
  (values : List Int) (h : values.length > 0)
  (original : Option TreeNode) (h₁ : original = build_tree_from_list values)
  (cloned : Option TreeNode) (h₂ : cloned = clone_tree original) :
  match getTargetCopy original cloned original, original with
  | some result, some orig => TreeNode.val result = TreeNode.val orig
  | _, _ => False :=
  sorry
-- </vc-theorems>