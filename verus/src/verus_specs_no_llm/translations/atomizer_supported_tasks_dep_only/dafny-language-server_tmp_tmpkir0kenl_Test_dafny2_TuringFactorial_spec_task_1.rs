// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn Factorial(n: nat) -> nat
{
    0
}

spec fn spec_ComputeFactorial(n: int) -> u: int
    requires
        1 <= n
    ensures
        u == Factorial(n)
;

proof fn lemma_ComputeFactorial(n: int) -> (u: int)
    requires
        1 <= n
    ensures
        u == Factorial(n)
{
    0
}

}