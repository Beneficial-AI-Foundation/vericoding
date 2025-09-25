-- <vc-preamble>
def maxLevelSum : Tree Int → Nat
  | _ => sorry

def getLevelSums : Tree Int → List Int 
  | _ => sorry

def height : Tree Int → Nat
  | _ => sorry

def completeTree : Int → Nat → Tree Int
  | _ , _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum : List Int → Int 
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maxLevelSum_positive (t : Tree Int) :
  maxLevelSum t ≥ 1 := sorry

theorem maxLevelSum_is_level_with_max_sum (t : Tree Int) :
  ∃ (sums : List Int), 
    sums = getLevelSums t ∧ 
    ∀ (level : Nat), level ≤ height t → 
      sum (getLevelSums t) ≥ sum (getLevelSums t) := sorry

theorem maxLevelSum_single_node (x : Int) :
  maxLevelSum (Tree.node x Tree.leaf Tree.leaf) = 1 := sorry

theorem maxLevelSum_complete_height_2 (x y z : Int) :
  maxLevelSum (Tree.node x 
                (Tree.node y Tree.leaf Tree.leaf)
                (Tree.node z Tree.leaf Tree.leaf)) = 1 := sorry

theorem maxLevelSum_same_values (x : Int) (h : Nat) :
  maxLevelSum (completeTree x h) = 1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval maxLevelSum TreeNode(1)

/-
info: 2
-/
-- #guard_msgs in
-- #eval maxLevelSum TreeNode(989)
-- </vc-theorems>