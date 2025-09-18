

/-!
{
"name": "dafny-synthesis_task_id_755_SecondSmallest",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_755_SecondSmallest",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
MinPair function that returns the minimum of two elements in a sequence.
-/
def MinPair (s : Array Int) : Int :=
sorry

/--
Specification for MinPair function
-/
theorem MinPair_spec (s : Array Int) :
s.size = 2 →
((s[0]! ≤ s[1]!) → MinPair s = s[0]!) ∧
((s[0]! > s[1]!) → MinPair s = s[1]!) := sorry

/--
min function that returns the minimum element in a sequence
-/
def min (s : Array Int) : Int :=
sorry

/--
Specification for min function
-/
theorem min_spec (s : Array Int) :
s.size ≥ 2 →
∀ i, 0 ≤ i ∧ i < s.size → min s ≤ s[i]! := sorry

/--
SecondSmallest method that returns the second smallest element in an array
-/
def SecondSmallest (s : Array Int) : Int :=
sorry

/--
Specification for SecondSmallest method
-/
theorem SecondSmallest_spec (s : Array Int) (result : Int) :
s.size ≥ 2 →
(∃ i j, 0 ≤ i ∧ i < s.size ∧ 0 ≤ j ∧ j < s.size ∧ i ≠ j ∧ s[i]! = min s ∧ s[j]! ≠ s[i]!) →
(∃ i j, 0 ≤ i ∧ i < s.size ∧ 0 ≤ j ∧ j < s.size ∧ i ≠ j ∧ s[i]! = min s ∧ s[j]! = result) ∧
(∀ k, 0 ≤ k ∧ k < s.size ∧ s[k]! ≠ min s → s[k]! ≥ result) := sorry
