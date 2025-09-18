-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count {α} [BEq α] (a : α) (xs : List α) : Nat :=
  sorry

def solve {α} [BEq α] (array1 array2 : List α) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_properties {α} [BEq α] (array1 array2 : List α)
  (h1 : array1 ≠ []) (h2 : array2 ≠ []) :
  let result := solve array1 array2;

  result.length = array2.length

  ∧ (∀ i elem, i < array2.length → array2.get ⟨i, by sorry⟩ = elem →
      result.get ⟨i, by sorry⟩ = count elem array1)

  ∧ ∀ x ∈ result, x ≤ array1.length :=
sorry

theorem solve_identical_arrays {α} [BEq α] (array : List α)
  (h : array ≠ []) :
  let result := solve array array;
  ∀ i c x, i < array.length →
    result.get ⟨i, by sorry⟩ = c →
    array.get ⟨i, by sorry⟩ = x →
    c = count x array :=
sorry

theorem solve_unique_array2 {α} [BEq α] (array1 array2 : List α)
  (h1 : array1 ≠ []) (h2 : array2 ≠ [])
  (unique : ∀ i j, i < array2.length → j < array2.length → i ≠ j →
    array2.get ⟨i, by sorry⟩ ≠ array2.get ⟨j, by sorry⟩) :
  solve array1 array2 = array2.map (λ x => count x array1) :=
sorry
-- </vc-theorems>