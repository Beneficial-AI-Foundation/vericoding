

/-!
{
"name": "dafny-synthesis_task_id_476_SumMinMax",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_476_SumMinMax",
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

/-- Specification for Min function -/
theorem Min_spec (a : Array Int) :
a.size > 0 → Min_ a = Min_ a := sorry

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

/-- Specification for Max function -/
theorem Max_spec (a : Array Int) :
a.size > 0 → Max_ a = Max_ a := sorry

/-- Returns the sum of minimum and maximum values in the array -/
def SumMinMax (a : Array Int) : Int :=
Max_ a + Min_ a

/-- Specification for SumMinMax method -/
theorem SumMinMax_spec (a : Array Int) :
a.size > 0 → SumMinMax a = Max_ a + Min_ a := sorry
