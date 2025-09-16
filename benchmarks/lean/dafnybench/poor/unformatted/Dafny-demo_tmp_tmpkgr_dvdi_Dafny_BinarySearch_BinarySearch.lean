

/-!
{
"name": "Dafny-demo_tmp_tmpkgr_dvdi_Dafny_BinarySearch_BinarySearch",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny-demo_tmp_tmpkgr_dvdi_Dafny_BinarySearch_BinarySearch",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Predicate indicating if an array is sorted between indices l and u.
Translated from Dafny's sorted predicate.
-/
def sorted (a : Array Int) (l : Int) (u : Int) : Prop :=
∀ i j, 0 ≤ l ∧ l ≤ i ∧ i ≤ j ∧ j ≤ u ∧ u < a.size → a[i.toNat]! ≤ a[j.toNat]!

/--
Binary search implementation translated from Dafny.
Returns index of key if found, negative number if not found.
-/
def BinarySearch (a : Array Int) (key : Int) : Int :=
sorry

/--
Specification for binary search:
1. If returned index is non-negative, key is found at that index
2. If returned index is negative, key is not present in array
-/
theorem BinarySearch_spec (a : Array Int) (key : Int) :
sorted a 0 (a.size - 1) →
let index := BinarySearch a key
(index ≥ 0 → index < a.size ∧ a[index.toNat]! = key) ∧
(index < 0 → ∀ k, 0 ≤ k ∧ k < a.size → a[k]! ≠ key) := sorry
