-- <vc-helpers>
-- </vc-helpers>

def findDuplicate (nums : List Nat) : Option Nat :=
  sorry

theorem emptyListReturnNone :
  findDuplicate [] = none := by sorry

theorem findsDuplicateInList1 :
  findDuplicate [1, 3, 4, 2, 2] = some 2 := by sorry

theorem findsDuplicateInList2 :
  findDuplicate [3, 1, 3, 4, 2] = some 3 := by sorry

theorem findsDuplicateInList3 :
  findDuplicate [2, 2, 2, 2, 2] = some 2 := by sorry

theorem findsDuplicateInList4 :
  findDuplicate [1, 1] = some 1 := by sorry

theorem minimalCaseFindsOne :
  findDuplicate [1, 1] = some 1 := by sorry

theorem findsInLargerList :
  findDuplicate [1, 2, 3, 4, 5, 6, 7, 8, 9, 5] = some 5 := by sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_duplicate [1, 3, 4, 2, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_duplicate [3, 1, 3, 4, 2]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_duplicate [2, 2, 2, 2, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded