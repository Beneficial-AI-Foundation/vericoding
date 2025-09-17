

/-!
{
"name": "Workshop_tmp_tmp0cu11bdq_Lecture_Answers_max_array_max",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Workshop_tmp_tmp0cu11bdq_Lecture_Answers_max_array_max",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Finds the maximum value in an array of integers.

@param a The input array of integers
@return The maximum value in the array

Translation of Dafny method:
dafny
method max(a:array<int>) returns(max:int)
requires a != null;
ensures forall j :: j >= 0 && j < a.Length ==> max >= a;
ensures a.Length > 0 ==> exists j :: j >= 0 && j < a.Length && max == a;

-/
def max (a : Array Int) : Int := sorry

/-- Specification for max function -/
theorem max_spec (a : Array Int) :
-- First ensures clause: max is larger than anything in array
(∀ j:Nat, 0 ≤ j ∧ j < a.size → max a ≥ a[j]!) ∧
-- Second ensures clause: if array non-empty, max exists in array
(a.size > 0 → ∃ j, 0 ≤ j ∧ j < a.size ∧ max a = a[j]!) := sorry
