

/-!
{
"name": "Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_InsertionSort_InsertionSort",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_advanced examples_InsertionSort_InsertionSort",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Predicate indicating if an array is sorted between start and end indices.
Translated from Dafny's sorted predicate.
-/
def sorted (a : Array Int) (start : Nat) (end_ : Nat) : Prop :=
a.size > 0 ∧
0 ≤ start ∧ start ≤ end_ ∧ end_ ≤ a.size ∧
∀ j k, start ≤ j ∧ j < k ∧ k < end_ → a[j]! ≤ a[k]!

/--
InsertionSort method specification translated from Dafny.
Takes an array of integers and sorts it in ascending order.
-/
def InsertionSort (a : Array Int) : Array Int :=
sorry

/--
Specification for InsertionSort method.
Requires array to be non-empty and length > 1.
Ensures array is sorted after execution.
-/
theorem InsertionSort_spec (a : Array Int) :
a.size > 1 →
sorted (InsertionSort a) 0 (InsertionSort a).size :=
sorry
