

/-!
{
"name": "DafnyProjects_tmp_tmp2acw_s4s_partitionOddEven_partitionOddEven",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: DafnyProjects_tmp_tmp2acw_s4s_partitionOddEven_partitionOddEven",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate indicating if a natural number is odd -/
def odd (n : Nat) : Bool := n % 2 = 1

/-- Predicate indicating if a natural number is even -/
def even (n : Nat) : Bool := n % 2 = 0

/--
Rearranges elements in an array of natural numbers so that all odd numbers appear before even numbers.

@param a Array of natural numbers to be partitioned
-/
def partitionOddEven (a : Array Nat) : Array Nat := sorry

/--
Specification for partitionOddEven:
1. The output array contains the same elements as the input array
2. No even number appears before an odd number in the output array
-/
theorem partitionOddEven_spec (a : Array Nat) :
let result := partitionOddEven a;
-- Output has same elements as input (using multiset equality)
result.size = a.size
-- No even number before odd number
∧ ¬(∃ i j, 0 ≤ i ∧ i < j ∧ j < result.size ∧ even (result[i]!) ∧ odd (result[j]!)) := sorry
