

/-!
{
"name": "CVS-handout1_tmp_tmptm52no3k_1_query",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: CVS-handout1_tmp_tmptm52no3k_1_query",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Recursive sum function over array slice from index i to j -/
partial def sum (a : Array Int) (i j : Int) : Int :=
if i = j then 0
else a[i.toNat]! + sum a (i+1) j

/-- Predicate checking if array c is a prefix sum of array a -/
def is_prefix_sum_for (a c : Array Int) : Prop :=
a.size + 1 = c.size ∧
c[0]! = 0 ∧
∀ i, 0 ≤ i ∧ i < a.size → c[(i+1)]! = c[i]! + a[i]!

/-- Query method specification -/
theorem query_spec (a : Array Int) (i j : Int) :
0 ≤ i ∧ i ≤ j ∧ j ≤ a.size →
∃ res, res = sum a i j := sorry

/-- Query method implementation -/
def query (a : Array Int) (i j : Int) : Int := sorry
