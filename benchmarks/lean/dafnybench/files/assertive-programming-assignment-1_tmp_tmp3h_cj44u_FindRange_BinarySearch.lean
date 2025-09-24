-- <vc-preamble>
def Sorted (q : Array Int) : Prop :=
∀ i j, 0 ≤ i → i ≤ j → j < q.size → q[i]! ≤ q[j]!
def RangeSatisfiesComparer (q : Array Int) (key : Int) (lowerBound upperBound : Nat)
(comparer : Int → Int → Bool ) : Prop :=
0 ≤ lowerBound ∧ lowerBound ≤ upperBound ∧ upperBound ≤ q.size →
∀ i, lowerBound ≤ i → i < upperBound → comparer (q[i]!) key = true
def RangeSatisfiesComparerNegation (q : Array Int) (key : Int) (lowerBound upperBound : Nat)
(comparer : Int → Int → Bool) : Prop :=
RangeSatisfiesComparer q key lowerBound upperBound (fun n1 n2 => ¬(comparer n1 n2))
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def BinarySearch (q : Array Int) (key : Int) (lowerBound upperBound : Nat)
(comparer : Int → Int → Bool) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
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
RangeSatisfiesComparer q key index q.size comparer :=
sorry
-- </vc-theorems>