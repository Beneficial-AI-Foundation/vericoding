-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def similarity (xs ys : List Int) : Float := sorry

theorem similarity_self_identity (xs : List Int) :
  similarity xs xs = (if xs.isEmpty then 0.0 else 1.0) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem similarity_symmetric (xs ys : List Int) :
  similarity xs ys = similarity ys xs := sorry

theorem similarity_bounds (xs ys : List Int) :
  0 ≤ similarity xs ys ∧ similarity xs ys ≤ 1 := sorry

theorem disjoint_similarity (xs ys : List Int) :
  xs ≠ [] → ys ≠ [] → (∀ y ∈ ys, y ∉ xs) → similarity xs ys = 0 := sorry 

theorem empty_list_similarity (xs : List Int) :
  similarity xs [] = 0 ∧ similarity [] xs = 0 ∧ similarity [] [] = 0 := sorry
-- </vc-theorems>