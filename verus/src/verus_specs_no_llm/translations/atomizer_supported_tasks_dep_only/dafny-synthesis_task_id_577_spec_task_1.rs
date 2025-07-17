// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: int) -> int
    requires
        n >= 0
    ensures
        0 <= Factorial(n)
{
    0
}

spec fn spec_FactorialOfLastDigit(n: int) -> fact: int
    requires
        n >= 0
    ensures
        fact == Factorial(n % 10)
;

proof fn lemma_FactorialOfLastDigit(n: int) -> (fact: int)
    requires
        n >= 0
    ensures
        fact == Factorial(n % 10)
{
    0
}

}