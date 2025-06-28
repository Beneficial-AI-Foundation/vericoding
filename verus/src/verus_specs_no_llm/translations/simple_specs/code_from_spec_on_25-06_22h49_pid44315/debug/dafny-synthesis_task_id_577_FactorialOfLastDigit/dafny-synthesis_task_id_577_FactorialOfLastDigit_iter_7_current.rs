use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: int) -> int
    decreases n
{
    if n <= 0 {
        1
    } else {
        n * Factorial(n - 1)
    }
}

// Helper lemma to prove factorial values for digits 0-9
proof fn lemma_factorial_digits()
    ensures
        Factorial(0) == 1,
        Factorial(1) == 1,
        Factorial(2) == 2,
        Factorial(3) == 6,
        Factorial(4) == 24,
        Factorial(5) == 120,
        Factorial(6) == 720,
        Factorial(7) == 5040,
        Factorial(8) == 40320,
        Factorial(9) == 362880,
{
    // The factorial values are proven by the recursive definition
}

// Helper lemma to prove that n % 10 is always between 0 and 9 for non-negative n
proof fn lemma_mod_10_range(n: int)
    requires n >= 0
    ensures 0 <= n % 10 <= 9
{
}

// Helper lemma to prove factorial for specific digit values
proof fn lemma_factorial_by_digit(digit: int)
    requires 0 <= digit <= 9
    ensures 
        (digit == 0 ==> Factorial(digit) == 1) &&
        (digit == 1 ==> Factorial(digit) == 1) &&
        (digit == 2 ==> Factorial(digit) == 2) &&
        (digit == 3 ==> Factorial(digit) == 6) &&
        (digit == 4 ==> Factorial(digit) == 24) &&
        (digit == 5 ==> Factorial(digit) == 120) &&
        (digit == 6 ==> Factorial(digit) == 720) &&
        (digit == 7 ==> Factorial(digit) == 5040) &&
        (digit == 8 ==> Factorial(digit) == 40320) &&
        (digit == 9 ==> Factorial(digit) == 362880)
{
    lemma_factorial_digits();
}

fn FactorialOfLastDigit(n: int) -> (fact: int)
    requires
        n >= 0
    ensures
        fact == Factorial(n % 10)
{
    let last_digit = n % 10;
    
    proof {
        lemma_mod_10_range(n);
        lemma_factorial_digits();
        lemma_factorial_by_digit(last_digit);
    }
    
    // Since n >= 0, we know that 0 <= last_digit <= 9
    // We can compute factorial directly for these small values
    let result = if last_digit == 0 {
        1
    } else if last_digit == 1 {
        1
    } else if last_digit == 2 {
        2
    } else if last_digit == 3 {
        6
    } else if last_digit == 4 {
        24
    } else if last_digit == 5 {
        120
    } else if last_digit == 6 {
        720
    } else if last_digit == 7 {
        5040
    } else if last_digit == 8 {
        40320
    } else { // last_digit == 9
        362880
    };
    
    result
}

}