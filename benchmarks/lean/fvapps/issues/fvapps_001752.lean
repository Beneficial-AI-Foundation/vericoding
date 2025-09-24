-- <vc-preamble>
def build_tree (values : List Int) : Option TreeNode := sorry
def lcaDeepestLeaves (root : TreeNode) : TreeNode := sorry

def get_depth (node : TreeNode) : Int := sorry
def get_leaves_at_depth (node : TreeNode) (target_depth : Int) (current_depth : Int := 0) : List TreeNode := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_node (node target : TreeNode) : Bool := sorry

theorem lca_deepest_leaves_in_tree (values : List Int) (tree : TreeNode) 
  (h1 : build_tree values = some tree) :
  find_node tree (lcaDeepestLeaves tree) = true := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lca_deepest_leaves_contains_all_deepest_leaves (values : List Int) (tree : TreeNode)
  (h1 : build_tree values = some tree)
  (max_depth : Int)
  (h2 : max_depth = get_depth tree)
  (deepest_leaves : List TreeNode) 
  (h3 : deepest_leaves = get_leaves_at_depth tree max_depth) :
  ∀ leaf, leaf ∈ deepest_leaves → find_node (lcaDeepestLeaves tree) leaf = true := sorry
-- </vc-theorems>