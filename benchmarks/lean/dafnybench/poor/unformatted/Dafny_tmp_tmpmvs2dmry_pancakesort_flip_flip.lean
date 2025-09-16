

/-!
{
"name": "Dafny_tmp_tmpmvs2dmry_pancakesort_flip_flip",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny_tmp_tmpmvs2dmry_pancakesort_flip_flip",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Flips (reverses) array elements in the range

@param a The array to flip elements in
@param num The upper bound index of elements to flip
-/
def flip (a : Array Int) (num : Int) : Array Int := sorry

/--
Specification for flip method:
- Requires array length > 0
- Requires num is valid index
- Ensures elements up to num are flipped
- Ensures elements after num are unchanged
-/
theorem flip_spec (a : Array Int) (num : Int) :
a.size > 0 →
0 ≤ num →
num < a.size →
let a' := flip a num
(∀ k, 0 ≤ k ∧ k ≤ num → a'[k.toNat]! = a[(num - k).toNat]!) ∧
(∀ k, num < k ∧ k < a.size → a'[k.toNat]! = a[k.toNat]!) := sorry
