// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Index(n: int) -> i: int
    requires
        1 <= n
    ensures
        0 <= i < n
;

proof fn lemma_Index(n: int) -> (i: int)
    requires
        1 <= n
    ensures
        0 <= i < n
{
    0
}

}