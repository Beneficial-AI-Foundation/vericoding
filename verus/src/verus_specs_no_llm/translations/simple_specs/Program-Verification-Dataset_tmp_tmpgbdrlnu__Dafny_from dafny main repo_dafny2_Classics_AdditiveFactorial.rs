// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn Factorial(n: nat) -> (nat)
{
    0
}

spec fn spec_AdditiveFactorial(n: nat) -> u: nat
    ensures
        u == Factorial(n)
;

proof fn lemma_AdditiveFactorial(n: nat) -> (u: nat)
    ensures
        u == Factorial(n)
{
    0
}

}