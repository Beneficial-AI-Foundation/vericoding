

/-!
{
"name": "Dafny_Programs_tmp_tmp99966ew4_lemma_FindZero",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny_Programs_tmp_tmp99966ew4_lemma_FindZero",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
FindZero method translated from Dafny.
Takes an array of integers and returns an index where zero is found.

Requirements:
- Array must not be null
- All elements must be non-negative
- Array must be monotonically increasing with max step of 1

Ensures:
- If returned index is negative, array contains no zeros
- If returned index is non-negative, it points to a zero element
-/
def FindZero (a : Array Int) : Int := sorry

/--
Specification for FindZero method
-/
theorem FindZero_spec (a : Array Int) :
(∀ i : Nat, i < a.size → 0 ≤ a[i]!) →
(∀ i : Nat, 0 < i ∧ i < a.size → (a[i]!) - 1 ≤ a[i]!) →
let index := FindZero a
(index < 0 → (∀ i : Nat, i < a.size → a[i]! ≠ 0)) ∧
(0 ≤ index → index < a.size ∧ a[index.toNat]! = 0) := sorry
