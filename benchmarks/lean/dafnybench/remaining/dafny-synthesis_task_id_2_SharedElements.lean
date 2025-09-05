import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_2_SharedElements",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_2_SharedElements",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Predicate indicating if an element exists in an array
-/
def InArray (a : Array Int) (x : Int) : Bool :=
  ∃ i, 0 ≤ i ∧ i < a.size ∧ a.get ⟨i⟩ = x

/--
SharedElements takes two arrays and returns an array containing elements present in both input arrays.
The output array contains no duplicates.
-/
def SharedElements (a : Array Int) (b : Array Int) : Array Int := sorry

/--
Specification for SharedElements:
1. All elements in the output are in both input arrays
2. The elements in the output are all different
-/
theorem SharedElements_spec (a b : Array Int) (result : Array Int) :
  (result = SharedElements a b) →
  (∀ x, x ∈ result.data → (InArray a x ∧ InArray b x)) ∧
  (∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result.get ⟨i⟩ ≠ result.get ⟨j⟩) := sorry

end DafnyBenchmarks