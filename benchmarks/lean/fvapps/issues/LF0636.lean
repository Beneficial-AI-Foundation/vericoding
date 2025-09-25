-- <vc-preamble>
def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_deleted_value (n k v : Nat) (arr : List Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_deleted_value_output_valid {n k v : Nat} {arr : List Nat} :
  let result := find_deleted_value n k v arr
  result = -1 ∨ result > 0 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_deleted_value 3 3 4 [2, 7, 3]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_deleted_value 3 1 4 [7, 6, 5]

/-
info: -1
-/
-- #guard_msgs in
-- #eval find_deleted_value 3 3 4 [2, 8, 3]
-- </vc-theorems>