// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumInts(n: int) -> int
    requires
        n >= 0
{
    0
}

spec fn spec_SumIntsLoop(n: int) -> s: int
    requires
        n >= 0
    ensures
        s == sumInts(n),
        s == n*(n+1)/2
;

proof fn lemma_SumIntsLoop(n: int) -> (s: int)
    requires
        n >= 0
    ensures
        s == sumInts(n),
        s == n*(n+1)/2
{
    0
}

}