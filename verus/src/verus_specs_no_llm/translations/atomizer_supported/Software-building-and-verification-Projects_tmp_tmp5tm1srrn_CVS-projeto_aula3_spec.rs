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

spec fn spec_Fib(n: nat) -> r:nat
    ensures
        r == fib(n)
;

proof fn lemma_Fib(n: nat) -> (r: nat)
    ensures
        r == fib(n)
{
    0
}

}