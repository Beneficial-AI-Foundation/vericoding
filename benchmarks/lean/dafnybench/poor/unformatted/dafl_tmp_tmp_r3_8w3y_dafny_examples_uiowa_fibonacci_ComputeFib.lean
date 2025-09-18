

/-!
{
"name": "dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_fibonacci_ComputeFib",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafl_tmp_tmp_r3_8w3y_dafny_examples_uiowa_fibonacci_ComputeFib",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Recursive definition of the Fibonacci sequence:
fib(0) = 0
fib(1) = 1
fib(n) = fib(n-1) + fib(n-2) for n ≥ 2
-/
def fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

/--
ComputeFib method computes the nth Fibonacci number.
Input: n - A natural number
Output: f - The nth Fibonacci number
Ensures: f equals fib(n)
-/
def ComputeFib (n : Nat) : Nat := sorry

/--
Specification for ComputeFib method:
For any natural number n, ComputeFib returns the nth Fibonacci number
-/
theorem ComputeFib_spec (n : Nat) :
ComputeFib n = fib n := sorry
