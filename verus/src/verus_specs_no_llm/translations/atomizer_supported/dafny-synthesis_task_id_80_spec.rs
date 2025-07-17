// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_TetrahedralNumber(n: int) -> t: int
    requires
        n >= 0
    ensures
        t == n * (n + 1) * (n + 2) / 6
;

proof fn lemma_TetrahedralNumber(n: int) -> (t: int)
    requires
        n >= 0
    ensures
        t == n * (n + 1) * (n + 2) / 6
{
    0
}

}