

/-!
{
"name": "Correctness_tmp_tmpwqvg5q_4_Sorting_Tangent_Tangent",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Correctness_tmp_tmpwqvg5q_4_Sorting_Tangent_Tangent",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
BinarySearch method translated from Dafny.
Takes a sorted array and finds insertion point for a value.
-/
def BinarySearch (a : Array Int) (circle : Int) : Int := sorry

/--
Specification for BinarySearch method
-/
theorem BinarySearch_spec (a : Array Int) (circle : Int) (n : Int) :
(∀ i, 1 ≤ i ∧ i < a.size → a[(i-1)]! < a[i]!) →
(∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! < a[j]!) →
0 ≤ n ∧ n ≤ a.size ∧
(∀ i, 0 ≤ i ∧ i < n → a[i.toNat]! < circle) ∧
(∀ i, n ≤ i ∧ i < a.size → circle ≤ a[i.toNat]!) := sorry

/--
Tangent method translated from Dafny.
Checks if there are matching elements between two arrays.
-/
def Tangent (r : Array Int) (x : Array Int) : Bool := sorry

/--
Specification for Tangent method
-/
theorem Tangent_spec (r x : Array Int) (found : Bool) :
(∀ i, 1 ≤ i ∧ i < x.size → x[(i-1)]! < x[i]!) →
(∀ i j, 0 ≤ i ∧ i < j ∧ j < x.size → x[i]! < x[j]!) →
(¬found →
(∀ i j, 0 ≤ i ∧ i < r.size ∧ 0 ≤ j ∧ j < x.size → r[i]! ≠ x[j]!)) ∧
(found →
(∃ i j, 0 ≤ i ∧ i < r.size ∧ 0 ≤ j ∧ j < x.size ∧ r[i]! = x[j]!)) := sorry
