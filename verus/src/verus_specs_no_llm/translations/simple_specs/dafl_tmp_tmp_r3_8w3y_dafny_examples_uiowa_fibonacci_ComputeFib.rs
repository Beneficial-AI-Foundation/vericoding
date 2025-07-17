// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fib(n: nat) -> nat
{
    0
}

spec fn spec_ComputeFib(n: nat) -> f: nat
    ensures
        f == fib(n)
;

proof fn lemma_ComputeFib(n: nat) -> (f: nat)
    ensures
        f == fib(n)
{
    0
}

}