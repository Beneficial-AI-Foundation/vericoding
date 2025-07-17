// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_UpWhileNotEqual(N: int) -> i: int
    requires
        0 <= N
    ensures
        i == N
;

proof fn lemma_UpWhileNotEqual(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == N
{
    0
}

}