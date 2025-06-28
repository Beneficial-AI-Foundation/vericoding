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
    // These will be proven by unfolding the definition
}

// Helper lemma to prove that n % 10 is always between 0 and 9 for non-negative n
proof fn lemma_mod_10_range(n: int)
    requires n >= 0
    ensures 0 <= n % 10 <= 9
{
    // This is a mathematical property that Verus can prove automatically
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
    }
    
    // Since n >= 0, we know that 0 <= last_digit <= 9
    // We can compute factorial directly for these small values
    if last_digit == 0 {
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
    }
}

}