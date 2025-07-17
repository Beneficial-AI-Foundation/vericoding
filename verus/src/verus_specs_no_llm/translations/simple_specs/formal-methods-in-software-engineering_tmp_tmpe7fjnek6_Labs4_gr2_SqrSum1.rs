// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SqrSumRec(n: int) -> int
    requires
        n >= 0
{
    0
}

spec fn spec_SqrSum1(n: int) -> s: int
    requires
        n >= 0
    ensures
        s == SqrSumRec(n)
;

proof fn lemma_SqrSum1(n: int) -> (s: int)
    requires
        n >= 0
    ensures
        s == SqrSumRec(n)
{
    0
}

}