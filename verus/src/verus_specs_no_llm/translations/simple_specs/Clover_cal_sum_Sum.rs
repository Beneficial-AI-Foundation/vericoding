// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Sum(N: int) -> s:int
    requires
        N >= 0
    ensures
        s == N * (N + 1) / 2
;

proof fn lemma_Sum(N: int) -> (s: int)
    requires
        N >= 0
    ensures
        s == N * (N + 1) / 2
{
    0
}

}