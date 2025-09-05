import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_807_FindFirstOdd",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_807_FindFirstOdd",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- Predicate indicating if a number is odd -/
def IsOdd (x : Int) : Bool :=
  x % 2 ≠ 0

/-- FindFirstOdd takes an array of integers and returns:
    - found: whether an odd number was found
    - index: the index of the first odd number if found
-/
def FindFirstOdd (a : Array Int) : Bool × Int := sorry

/-- Specification for FindFirstOdd:
    - If no odd number is found, then all elements are even
    - If an odd number is found, then:
      * The index is valid
      * The element at index is odd
      * All elements before index are even
-/
theorem FindFirstOdd_spec (a : Array Int) (result : Bool × Int) :
  let (found, index) := result
  (¬found → ∀ i, 0 ≤ i ∧ i < a.size → ¬IsOdd (a.get ⟨i⟩)) ∧
  (found → 0 ≤ index ∧ index < a.size ∧ 
           IsOdd (a.get ⟨index⟩) ∧
           ∀ i, 0 ≤ i ∧ i < index → ¬IsOdd (a.get ⟨i⟩)) := sorry

end DafnyBenchmarks