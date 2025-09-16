

/-!
{
"name": "assertive-programming-assignment-1_tmp_tmp3h_cj44u_FindRange_BinarySearch",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: assertive-programming-assignment-1_tmp_tmp3h_cj44u_FindRange_BinarySearch",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate indicating if an array is sorted in ascending order -/
def Sorted (q : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < q.size → q[i]! ≤ q[j]!

/-- Predicate indicating if all values in range satisfy the comparer function -/
def RangeSatisfiesComparer (q : Array Int) (key : Int) (lowerBound upperBound : Nat)
(comparer : Int → Int → Bool ) : Prop :=
0 ≤ lowerBound ∧ lowerBound ≤ upperBound ∧ upperBound ≤ q.size →
∀ i, lowerBound ≤ i → i < upperBound → comparer (q[i]!) key = true

/-- Predicate indicating if all values in range satisfy the negation of comparer function -/
def RangeSatisfiesComparerNegation (q : Array Int) (key : Int) (lowerBound upperBound : Nat)
(comparer : Int → Int → Bool) : Prop :=
RangeSatisfiesComparer q key lowerBound upperBound (fun n1 n2 => ¬(comparer n1 n2))

/-- Binary search implementation with specifications -/
def BinarySearch (q : Array Int) (key : Int) (lowerBound upperBound : Nat)
(comparer : Int → Int → Bool) : Nat := sorry

/-- Specification for BinarySearch -/
theorem BinarySearch_spec (q : Array Int) (key : Int) (lowerBound upperBound : Nat)
(comparer : Int → Int → Bool) :
Sorted q →
0 ≤ lowerBound → lowerBound ≤ upperBound → upperBound ≤ q.size →
RangeSatisfiesComparerNegation q key 0 lowerBound comparer →
RangeSatisfiesComparer q key upperBound q.size comparer →
(∀ n1 n2, comparer n1 n2 = (n1 > n2)) ∨
(∀ n1 n2, comparer n1 n2 = (n1 ≥ n2)) →
let index := BinarySearch q key lowerBound upperBound comparer
lowerBound ≤ index ∧ index ≤ upperBound ∧
RangeSatisfiesComparerNegation q key 0 index comparer ∧
RangeSatisfiesComparer q key index q.size comparer := sorry
