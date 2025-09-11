-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_serialization (s : String) : Bool := sorry

theorem slot_balance_for_valid_serializations {preorder : String} :
  is_valid_serialization preorder →
  let nodes := preorder.splitOn ","
  let final_slot := nodes.foldl (fun slot node =>
    if node = "#" then slot - 1 else slot + 1
  ) 1
  final_slot = 0 := 
sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded