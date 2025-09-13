import Std

open Std.Do

/-!
{
  "name": "dafny_tmp_tmp59p638nn_examples_SelectionSort_SelectionnSort",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny_tmp_tmp59p638nn_examples_SelectionSort_SelectionnSort",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Predicate indicating that array elements in range [left,right) are preserved
between old and new states
-/
def Preserved (a : Array Int) (old_a : Array Int) (left right : Nat) : Prop :=
  left ≤ right ∧ right ≤ a.size ∧
  ∀ i, left ≤ i ∧ i < right → a.get ⟨i⟩ = old_a.get ⟨i⟩

/--
Predicate indicating array elements in range [left,right) are ordered
-/
def Ordered (a : Array Int) (left right : Nat) : Prop :=
  left ≤ right ∧ right ≤ a.size ∧
  ∀ i, 0 < left ∧ left ≤ i ∧ i < right → 
    a.get (i-1) ≤ a.get ⟨i⟩

/--
Predicate indicating array is sorted and elements are preserved
-/
def Sorted (a : Array Int) (old_a : Array Int) : Prop :=
  Ordered a 0 a.size ∧ Preserved a old_a 0 a.size

/--
Selection sort implementation and specification
-/
def SelectionnSort (a : Array Int) : Array Int :=
  sorry

/--
Main specification theorem for SelectionSort
-/
theorem SelectionnSort_spec (a : Array Int) :
  Sorted (SelectionnSort a) a := sorry

end DafnyBenchmarks