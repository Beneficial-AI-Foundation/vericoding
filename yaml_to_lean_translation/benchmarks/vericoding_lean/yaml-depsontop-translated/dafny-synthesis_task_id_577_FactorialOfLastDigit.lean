```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_577_FactorialOfLastDigit",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_577_FactorialOfLastDigit",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ["Factorial"],
  "methods": ["FactorialOfLastDigit"]
}
-/

namespace DafnyBenchmarks

/--
Computes the factorial of a non-negative integer.
Translated from Dafny's Factorial function.
-/
def Factorial (n : Int) : Int :=
  if n == 0 then 1
  else n * Factorial (n-1)

/--
Specification for Factorial function ensuring non-negativity of result
-/
theorem Factorial_spec (n : Int) :
  n ≥ 0 → Factorial n ≥ 0 := sorry

/--
Computes the factorial of the last digit of a number.
Translated from Dafny's FactorialOfLastDigit method.
-/
def FactorialOfLastDigit (n : Int) : Int := sorry

/--
Specification for FactorialOfLastDigit ensuring it returns
the factorial of the input's last digit
-/
theorem FactorialOfLastDigit_spec (n : Int) :
  n ≥ 0 → FactorialOfLastDigit n = Factorial (n % 10) := sorry

end DafnyBenchmarks
```