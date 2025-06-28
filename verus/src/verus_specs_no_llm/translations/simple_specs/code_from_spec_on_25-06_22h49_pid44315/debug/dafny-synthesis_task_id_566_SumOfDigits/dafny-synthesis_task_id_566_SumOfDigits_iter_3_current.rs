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
        let old_n = n;
        let old_result = result;
        
        // Extract the last digit
        let digit = n % 10;
        n = n / 10;
        result = result + digit;
        
        // Proof that the invariant is maintained
        assert(SumDigits(old_n) == digit + SumDigits(n));
        assert(old_result + SumDigits(old_n) == SumDigits(number));
        assert(result + SumDigits(n) == (old_result + digit) + SumDigits(n));
        assert(result + SumDigits(n) == old_result + (digit + SumDigits(n)));
        assert(result + SumDigits(n) == old_result + SumDigits(old_n));
        assert(result + SumDigits(n) == SumDigits(number));
    }
    
    // When n == 0, SumDigits(n) == 0, so result == SumDigits(number)
    assert(n == 0);
    assert(SumDigits(0) == 0);
    assert(result + SumDigits(n) == SumDigits(number));
    assert(result + 0 == SumDigits(number));
    
    result
}

}