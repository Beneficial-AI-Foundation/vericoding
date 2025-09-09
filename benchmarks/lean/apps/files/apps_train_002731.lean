-- <vc-helpers>
-- </vc-helpers>

def distinct {α} [BEq α] (xs : List α) : List α :=
  sorry

theorem distinct_uniqueness {α} [BEq α] (xs : List α) :
  let result := distinct xs
  ∀ a b, a ∈ result → b ∈ result → a = b → 
  List.findIdx (· == a) result = List.findIdx (· == b) result := by sorry

theorem distinct_preserves_order {α} [BEq α] (xs : List α) :
  let result := distinct xs
  ∀ (i j : Fin (List.length result)), i.val < j.val →
  let a := result[i]
  let b := result[j]
  List.findIdx (· == a) xs < List.findIdx (· == b) xs := by sorry

theorem distinct_maintains_membership {α} [BEq α] (xs : List α) :
  ∀ x, x ∈ distinct xs ↔ x ∈ xs := by sorry

theorem distinct_length {α} [BEq α] (xs : List α) :
  List.length (distinct xs) ≤ List.length xs := by sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval distinct [1]

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval distinct [1, 2]

/-
info: [1, 2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval distinct [1, 1, 1, 2, 3, 4, 5]

-- Apps difficulty: introductory
-- Assurance level: guarded