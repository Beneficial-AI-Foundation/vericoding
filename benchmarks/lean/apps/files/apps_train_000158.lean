/-
One way to serialize a binary tree is to use pre-order traversal. When we encounter a non-null node, we record the node's value. If it is a null node, we record using a sentinel value such as #.

     _9_
    /   \
   3     2
  / \   / \
 4   1  #  6
/ \ / \   / \
# # # #   # #

For example, the above binary tree can be serialized to the string "9,3,4,#,#,1,#,#,2,#,6,#,#", where # represents a null node.

Given a string of comma separated values, verify whether it is a correct preorder traversal serialization of a binary tree. Find an algorithm without reconstructing the tree.

Each comma separated value in the string must be either an integer or a character '#' representing null pointer.

You may assume that the input format is always valid, for example it could never contain two consecutive commas such as "1,,3".

Example 1:

Input: "9,3,4,#,#,1,#,#,2,#,6,#,#"
Output: true

Example 2:

Input: "1,#"
Output: false

Example 3:

Input: "9,#,#,1"
Output: false
-/

-- <vc-helpers>
-- </vc-helpers>

def is_valid_serialization (s : String) : Bool := sorry

theorem slot_balance_for_valid_serializations {preorder : String} :
  is_valid_serialization preorder →
  let nodes := preorder.splitOn ","
  let final_slot := nodes.foldl (fun slot node =>
    if node = "#" then slot - 1 else slot + 1
  ) 1
  final_slot = 0 := 
sorry

theorem all_nulls_valid_only_simple {preorder : String} :
  (∀ n ∈ preorder.splitOn ",", n = "#") →
  is_valid_serialization preorder →
  preorder = "#" ∨ preorder = "#,#" :=
sorry

theorem no_negative_slots_for_prefixes {preorder : String} {i : Nat} :
  let nodes := preorder.splitOn ","
  let slot := (nodes.take (i+1)).foldl (fun slot node => 
    if node = "#" then slot - 1 else slot + 1
  ) 1
  i < nodes.length →
  is_valid_serialization (String.intercalate "," (nodes.take (i+1))) →
  slot ≥ 0 :=
sorry

theorem trivial_cases :
  (¬ is_valid_serialization "") ∧
  (is_valid_serialization "#") ∧
  (¬ is_valid_serialization "1") :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_valid_serialization "9,3,4,#,#,1,#,#,2,#,6,#,#"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_valid_serialization "1,#"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_valid_serialization "9,#,#,1"

-- Apps difficulty: interview
-- Assurance level: unguarded