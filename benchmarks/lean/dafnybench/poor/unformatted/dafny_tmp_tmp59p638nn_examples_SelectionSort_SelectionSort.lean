

/-!
{
"name": "dafny_tmp_tmp59p638nn_examples_SelectionSort_SelectionSort",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny_tmp_tmp59p638nn_examples_SelectionSort_SelectionSort",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Predicate indicating that array elements in range [left,right) are preserved
between old and new states
-/
def Preserved (a : Array Int) (old_a : Array Int) (left : Nat) (right : Nat) : Prop :=
left ≤ right ∧ right ≤ a.size ∧
(∀ i, left ≤ i ∧ i < right → a[i]! = old_a[i]!)

/--
Predicate indicating array elements in range [left,right) are ordered
-/
def Ordered (a : Array Int) (left : Nat) (right : Nat) : Prop :=
left ≤ right ∧ right ≤ a.size ∧
(∀ i, 0 < left ∧ left ≤ i ∧ i < right → a[i-1]! ≤ a[i]!)

/--
Predicate indicating array is sorted and preserves elements
-/
def Sorted (a : Array Int) (old_a : Array Int) : Prop :=
Ordered a 0 a.size ∧ Preserved a old_a 0 a.size

/--
Selection sort implementation specification
-/
def SelectionSort (a : Array Int) : Array Int := sorry

/--
Selection sort correctness theorem
-/
theorem SelectionSort_spec (a : Array Int) :
let result := SelectionSort a
Sorted result a := sorry
