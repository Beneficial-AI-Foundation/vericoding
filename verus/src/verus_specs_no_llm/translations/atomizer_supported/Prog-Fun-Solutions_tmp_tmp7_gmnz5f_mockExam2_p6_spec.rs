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

spec fn spec_problem6(n: nat) -> a: int
    ensures
        a == fSum(n)
;

proof fn lemma_problem6(n: nat) -> (a: int)
    ensures
        a == fSum(n)
{
    0
}

}