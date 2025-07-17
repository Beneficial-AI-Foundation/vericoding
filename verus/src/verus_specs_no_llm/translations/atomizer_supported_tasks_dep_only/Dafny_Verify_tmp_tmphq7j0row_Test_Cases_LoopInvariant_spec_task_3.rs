// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_DownWhileNotEqual(N: int) -> i: int
    requires
        0 <= N
    ensures
        i == 0
;

proof fn lemma_DownWhileNotEqual(N: int) -> (i: int)
    requires
        0 <= N
    ensures
        i == 0
{
    0
}

}