// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_TriangleNumber(N: int) -> t: int
    requires
        N >= 0
    ensures
        t == N * (N + 1) / 2
;

proof fn lemma_TriangleNumber(N: int) -> (t: int)
    requires
        N >= 0
    ensures
        t == N * (N + 1) / 2
{
    0
}

}