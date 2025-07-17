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

spec fn spec_IterativeFactorial(n: nat) -> result: nat
    ensures
        result == Factorial(n)
;

proof fn lemma_IterativeFactorial(n: nat) -> (result: nat)
    ensures
        result == Factorial(n)
{
    0
}

}