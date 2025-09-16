

/-!
{
"name": "Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_handout1_queryFast",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Software-building-and-verification-Projects_tmp_tmp5tm1srrn_CVS-projeto_handout1_queryFast",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Computes sum of array elements from index i to j (exclusive) -/
partial def sum (a : Array Int) (i j : Int) : Int :=
if i = j then 0
else a[(j-1).toNat]! + sum a i (j-1)

/-- Predicate checking if array c is prefix sum of array a -/
def is_prefix_sum_for (a c : Array Int) : Prop :=
a.size + 1 = c.size ∧
∀ i, 0 ≤ i ∧ i ≤ a.size → c[i]! = sum a 0 i

/-- Main query function specification -/
def queryFast (a c : Array Int) (i j : Int) : Int :=
sorry

/-- Specification for queryFast -/
theorem queryFast_spec (a c : Array Int) (i j : Int) :
0 ≤ i → i ≤ j → j ≤ a.size →
is_prefix_sum_for a c →
queryFast a c i j = sum a i j := sorry
