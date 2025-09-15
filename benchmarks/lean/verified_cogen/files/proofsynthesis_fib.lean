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

def main : IO Unit := pure ()