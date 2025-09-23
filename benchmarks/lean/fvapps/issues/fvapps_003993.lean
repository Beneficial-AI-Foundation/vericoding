-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def unite_unique [BEq α] : List (List α) → List α
  | _ => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unite_unique_maintains_order [BEq α] (arrays : List (List α)) :
  let result := unite_unique arrays
  -- Result has no duplicates
  (∀ (i j : Fin result.length),
    result.get i = result.get j → i = j) ∧
  -- All input elements are present
  (∀ arr ∈ arrays, ∀ val ∈ arr, val ∈ result) ∧
  -- Order is preserved between arrays
  (∀ (i j : Fin result.length), i.val < j.val →
    let val := result.get j
    let prior_val := result.get i
    ∃ (array_idx₁ array_idx₂ : Nat), array_idx₁ ≤ array_idx₂ ∧ 
      array_idx₂ < arrays.length ∧
      prior_val ∈ arrays.get! array_idx₁ ∧
      val ∈ arrays.get! array_idx₂) :=
sorry

theorem unite_unique_bound [BEq α] (arrays : List (List α)) :
  let result := unite_unique arrays
  result.length ≤ (arrays.map List.length).foldl Nat.add 0 :=
sorry

theorem unite_unique_empty_arrays [BEq α] (arrays : List (List α)) :
  let result := unite_unique arrays
  let flattened := arrays.join
  -- Result has same elements as flattened arrays
  (∀ x, x ∈ result ↔ x ∈ flattened) ∧
  -- First occurrence property
  (∀ (i j : Fin result.length),
    result.get i = result.get j → i.val ≤ j.val) :=
sorry
-- </vc-theorems>