-- <vc-preamble>
-- Fibonacci specification function using Nat to avoid termination issues
def fibo : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fibo n + fibo (n + 1)

-- Helper function to check if fibonacci value fits in i32  
def fibo_fits_i32 (n : Nat) : Bool :=
  fibo n < 0x8000_0000

-- Precondition definitions
@[reducible, simp]
def fibonacci_precond (n : Nat) :=
  fibo_fits_i32 n ∧ n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fibonacci (n : Nat) (h_precond : fibonacci_precond n) : Array Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def fibonacci_postcond (n : Nat) (result: Array Int) (h_precond : fibonacci_precond n) :=
  (∀ i : Nat, 2 ≤ i ∧ i < n → result[i]! = (fibo i : Int)) ∧ result.size = n

theorem fibonacci_spec_satisfied (n: Nat) (h_precond : fibonacci_precond n) :
    fibonacci_postcond n (fibonacci n h_precond) h_precond := by
  sorry
-- </vc-theorems>