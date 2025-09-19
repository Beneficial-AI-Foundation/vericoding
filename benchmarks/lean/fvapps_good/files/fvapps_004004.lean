-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def comp : (List Int) → (List Int) → Bool := sorry

theorem comp_none_inputs (l : List Int) : 
  comp [] l = false ∨ comp l [] = false ∨ comp [] [] = false
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem comp_array_squared (arr : List Int) :
  let squared := arr.map (fun x => x * x)
  comp arr squared = true
  := sorry

theorem comp_different_lengths (arr1 arr2 : List Int) :
  arr1.length ≠ arr2.length → comp arr1 arr2 = false
  := sorry

theorem comp_permutations (arr : List Int) :
  arr ≠ [] →
  let squared := arr.map (fun x => x * x)
  let shuffled := squared.reverse
  comp arr shuffled = true
  := sorry

theorem comp_empty_arrays :
  comp [] [] = true ∧ 
  comp [] [1] = false ∧
  comp [1] [] = false
  := sorry
-- </vc-theorems>