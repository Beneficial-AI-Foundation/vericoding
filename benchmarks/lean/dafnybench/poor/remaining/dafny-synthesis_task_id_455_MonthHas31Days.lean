import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_455_MonthHas31Days",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_455_MonthHas31Days",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Determines if a given month has 31 days.

@param month The month number (1-12)
@return True if the month has 31 days, false otherwise
-/
def MonthHas31Days (month : Int) : Bool := sorry

/--
Specification for MonthHas31Days:
- Requires month is between 1 and 12 inclusive
- Ensures result is true iff month is one of {1,3,5,7,8,10,12}
-/
theorem MonthHas31Days_spec (month : Int) :
  1 ≤ month ∧ month ≤ 12 →
  MonthHas31Days month = true ↔ 
    (month = 1 ∨ month = 3 ∨ month = 5 ∨ month = 7 ∨ 
     month = 8 ∨ month = 10 ∨ month = 12) := sorry

end DafnyBenchmarks