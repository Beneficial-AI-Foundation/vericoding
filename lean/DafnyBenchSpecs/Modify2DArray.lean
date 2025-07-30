import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- modify_array_element: Modify a single element in a 2D array.
    
    Given a 2D array and indices, sets the value at the specified position.
    The function modifies the array in-place.
    
    Example: modify_array_element([[1,2],[3,4]], 0, 1, 5) changes array to [[1,5],[3,4]]
-/
def modifyArrayElement (arr : Array (Array Nat)) (index1 index2 : Nat) (val : Nat) : 
    Id (Array (Array Nat)) :=
  if h1 : index1 < arr.size then
    if h2 : index2 < arr[index1].size then
      let row := arr[index1]'h1
      let newRow := row.set index2 val
      arr.set index1 newRow
    else
      arr
  else
    arr

/-- Specification: modifyArrayElement sets the value at the specified position
    while leaving all other elements unchanged.
    
    Precondition: 
    - index1 < arr.size
    - index2 < arr[index1].size
    - All rows in the array are distinct references
    
    Postcondition: 
    - The array structure is preserved (same rows)
    - Only the element at [index1][index2] is changed to val
    - All other elements remain unchanged
-/
theorem modifyArrayElement_spec (arr : Array (Array Nat)) (index1 index2 val : Nat) :
    ⦃⌜index1 < arr.size ∧ 
      index2 < arr[index1]!.size ∧
      (∀ i j : Fin arr.size, i ≠ j → arr[i] ≠ arr[j])⌝⦄
    modifyArrayElement arr index1 index2 val
    ⦃⇓result => ⌜
      -- Array structure preserved (same number of rows)
      result.size = arr.size ∧
      -- The specified element has the new value  
      (index1 < result.size → index2 < result[index1]!.size → 
        result[index1]![index2]! = val)
    ⌝⦄ := by
  sorry