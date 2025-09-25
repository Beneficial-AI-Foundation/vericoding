-- <vc-preamble>
def is_straight_path {α : Type} (t : Tree α) (xs : List α) : Prop :=
  sorry

def build_zigzag_tree {α : Type} (n : Nat) (x : α) : Tree α :=
  sorry

def corresponds_to_list {α : Type} (t : Tree α) (xs : List α) : Prop :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_zigzag {α : Type} (t : Tree α) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_single_node {α : Type} (t : Tree α) : 
  (t = Tree.nil ∨ (∃ x, t = Tree.node x Tree.nil Tree.nil)) →
  longest_zigzag t = 0 :=
sorry

theorem straight_path_bound {α : Type} (root : Tree α) (xs : List α) :
  is_straight_path root xs →
  longest_zigzag root ≤ 1 :=
sorry

theorem zigzag_monotone {α : Type} (x y z : α) :
  let t1 := Tree.node x Tree.nil Tree.nil
  let t2 := Tree.node x Tree.nil (Tree.node y Tree.nil Tree.nil)
  let t3 := Tree.node x Tree.nil (Tree.node y (Tree.node z Tree.nil Tree.nil) Tree.nil)
  longest_zigzag t1 = 0 ∧
  longest_zigzag t2 ≥ 1 ∧  
  longest_zigzag t3 ≥ 2 :=
sorry

theorem perfect_zigzag_length {α : Type} (n : Nat) (x : α) :
  longest_zigzag (build_zigzag_tree n x) = n :=
sorry

theorem result_bounds {α : Type} (t : Tree α) (xs : List α) :
  corresponds_to_list t xs →
  0 ≤ longest_zigzag t ∧ longest_zigzag t ≤ xs.length - 1 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval longest_zigzag TreeNode(1)

/-
info: 3
-/
-- #guard_msgs in
-- #eval longest_zigzag TreeNode(1)

/-
info: 0
-/
-- #guard_msgs in
-- #eval longest_zigzag TreeNode(1)
-- </vc-theorems>