

/-!
{
"name": "dafny-synthesis_task_id_762_IsMonthWith30Days",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_762_IsMonthWith30Days",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Determines if a given month has 30 days.

@param month The month number (1-12)
@return True if the month has 30 days, false otherwise
-/
def IsMonthWith30Days (month : Int) : Bool := sorry

/--
Specification for IsMonthWith30Days:
- Requires month is between 1 and 12 inclusive
- Ensures result is true iff month is 4, 6, 9 or 11
-/
theorem IsMonthWith30Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
IsMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) := sorry
