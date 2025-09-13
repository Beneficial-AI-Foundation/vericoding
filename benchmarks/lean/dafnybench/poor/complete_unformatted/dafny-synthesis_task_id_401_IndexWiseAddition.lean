import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_401_IndexWiseAddition",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_401_IndexWiseAddition",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Adds two 2D arrays element-wise.
Input arrays must be non-empty and have matching dimensions.
Returns a new array containing the element-wise sums.
-/
def IndexWiseAddition (a b : Array (Array Int)) : Array (Array Int) := sorry

/--
Specification for IndexWiseAddition:
- Input arrays must be non-empty
- Input arrays must have same outer dimension
- Input arrays must have matching inner dimensions
- Output array has same dimensions as inputs
- Each element is sum of corresponding input elements
-/
theorem IndexWiseAddition_spec (a b : Array (Array Int)) :
  a.size > 0 ∧ b.size > 0 ∧
  a.size = b.size ∧
  (∀ i, 0 ≤ i ∧ i < a.size → (a[i]!).size = (b[i]!).size) →
  let result := IndexWiseAddition a b
  result.size = a.size ∧
  (∀ i, 0 ≤ i ∧ i < result.size → (result[i]!).size = (a[i]!).size) ∧
  (∀ i, 0 ≤ i ∧ i < result.size →
      ∀ j, 0 ≤ j ∧ j < (result[i]!).size →
      (result[i]!)[j]! = (a[i]!)[j]! + (b[i]!)[j]!) := sorry

end DafnyBenchmarks
