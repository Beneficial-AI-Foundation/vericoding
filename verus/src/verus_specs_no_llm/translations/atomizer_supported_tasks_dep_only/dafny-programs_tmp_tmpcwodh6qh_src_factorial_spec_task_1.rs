// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn fact(n: nat) -> nat
    ensures
        fact(n) >= 1
{
    0
}

spec fn spec_factorial(n: nat) -> res: nat
    ensures
        res == fact(n)
;

proof fn lemma_factorial(n: nat) -> (res: nat)
    ensures
        res == fact(n)
{
    0
}

}