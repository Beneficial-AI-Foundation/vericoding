-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distinct {α} [BEq α] (xs : List α) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>