// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn FactorialOfLastDigit(n: int) -> (fact: int)
    requires n >= 0
    ensures fact == Factorial(n % 10)
{
}

}