

/-!
{
"name": "dafny-synthesis_task_id_588_DifferenceMinMax",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_588_DifferenceMinMax",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Finds the minimum value in an array recursively -/
partial def Min_ (a : Array Int) : Int :=
if a.size = 1 then
a[0]!
else
let minPrefix := Min_ (a.extract 0 (a.size - 1))
if a[a.size - 1]! ≤ minPrefix then
a[a.size - 1]!
else
Min_ (a.extract 0 (a.size - 1))

/-- Finds the maximum value in an array recursively -/
partial def Max_ (a : Array Int) : Int :=
if a.size = 1 then
a[0]!
else
let maxPrefix := Max_ (a.extract 0 (a.size - 1))
if a[a.size - 1]! ≥ maxPrefix then
a[a.size - 1]!
else
Max_ (a.extract 0 (a.size - 1))

/-- Computes the difference between maximum and minimum values in an array -/
def DifferenceMinMax (a : Array Int) : Int :=
Max_ a - Min_ a

/-- Specification for DifferenceMinMax -/
theorem DifferenceMinMax_spec (a : Array Int) :
a.size > 0 →
DifferenceMinMax a = Max_ a - Min_ a := sorry
