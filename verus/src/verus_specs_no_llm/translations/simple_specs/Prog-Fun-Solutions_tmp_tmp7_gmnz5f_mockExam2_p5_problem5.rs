// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

proof fn f(n: int) -> (int)
{
    0
}

spec fn spec_problem5(n: nat) -> x: int
    ensures
        x == f(n)
;

proof fn lemma_problem5(n: nat) -> (x: int)
    ensures
        x == f(n)
{
    0
}

}