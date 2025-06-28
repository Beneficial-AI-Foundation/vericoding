use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SumDigits(number: nat) -> nat
    decreases number
{
    if number == 0 {
        0
    } else {
        (number % 10) + SumDigits(number / 10)
    }
}

proof fn lemma_sum_digits_decomposition(n: nat)
    requires n > 0
    ensures SumDigits(n) == (n % 10) + SumDigits(n / 10)
{
    // This follows directly from the definition of SumDigits
}

fn SumOfDigits(number: nat) -> (sum: nat)
    requires
        number >= 0
    ensures
        sum >= 0,
        sum == SumDigits(number)
{
    let mut n = number;
    let mut result = 0;
    
    while n > 0
        invariant
            result + SumDigits(n) == SumDigits(number),
            result >= 0,
            n >= 0
        decreases n
    {
        // Extract the last digit
        let digit = n % 10;
        let old_n = n;
        n = n / 10;
        result = result + digit;
        
        // Proof that the invariant is maintained
        proof {
            lemma_sum_digits_decomposition(old_n);
            assert(SumDigits(old_n) == digit + SumDigits(n));
            assert((result - digit) + SumDigits(old_n) == SumDigits(number));
            assert((result - digit) + (digit + SumDigits(n)) == SumDigits(number));
            assert(result + SumDigits(n) == SumDigits(number));
        }
    }
    
    // When n == 0, SumDigits(n) == 0, so result == SumDigits(number)
    proof {
        assert(n == 0);
        assert(SumDigits(0) == 0);
        assert(result + SumDigits(n) == SumDigits(number));
        assert(result == SumDigits(number));
    }
    
    result
}

}