// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_square(n: int) -> r: int
    requires
        0 <= n
    ensures
        r == n*n
;

proof fn lemma_square(n: int) -> (r: int)
    requires
        0 <= n
    ensures
        r == n*n
{
    0
}

}