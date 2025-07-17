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

spec fn spec_fibIter(n: nat) -> a:nat
    requires
        n > 0
    ensures
        a == fib(n)
;

proof fn lemma_fibIter(n: nat) -> (a: nat)
    requires
        n > 0
    ensures
        a == fib(n)
{
    0
}

}