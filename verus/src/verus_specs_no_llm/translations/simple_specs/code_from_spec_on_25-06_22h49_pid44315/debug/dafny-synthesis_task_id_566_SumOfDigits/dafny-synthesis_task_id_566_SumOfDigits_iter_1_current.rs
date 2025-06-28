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
            result >= 0
        decreases n
    {
        result = result + (n % 10);
        n = n / 10;
    }
    
    result
}

}