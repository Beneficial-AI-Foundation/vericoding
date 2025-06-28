// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn FactorialOfLastDigit(n: int) -> (fact: int)
    requires
        n >= 0
    ensures
        fact == Factorial(n % 10)
{
    return 0;
}

}