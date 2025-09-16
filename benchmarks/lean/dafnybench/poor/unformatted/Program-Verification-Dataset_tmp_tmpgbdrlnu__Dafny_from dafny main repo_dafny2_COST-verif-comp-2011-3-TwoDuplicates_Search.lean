

/-!
{
"name": "Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_COST-verif-comp-2011-3-TwoDuplicates_Search",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_from dafny main repo_dafny2_COST-verif-comp-2011-3-TwoDuplicates_Search",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Checks if a value appears twice in an array up to index k
-/
def IsPrefixDuplicate (a : Array Int) (k : Int) (p : Int) : Prop :=
∃ i j, 0 ≤ i ∧ i < j ∧ j < k ∧ a[i.toNat]! = p ∧ a[j.toNat]! = p

/--
Checks if a value appears twice in the full array
-/
def IsDuplicate (a : Array Int) (p : Int) : Prop :=
IsPrefixDuplicate a a.size p

/--
Search for two values that each appear twice in the array.
Returns a pair of such values.

Requirements:
- Array has at least 4 elements
- There exist two distinct values that each appear twice
- All array elements are between 0 and array.size-2
-/
def Search (a : Array Int) : (Int × Int) := sorry

/--
Specification for Search method
-/
theorem Search_spec (a : Array Int) :
(4 ≤ a.size) →
(∃ p q, p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q) →
(∀ i, 0 ≤ i ∧ i < a.size → 0 ≤ a[i]! ∧ a[i]! < a.size - 2) →
let (p, q) := Search a
p ≠ q ∧ IsDuplicate a p ∧ IsDuplicate a q := sorry
