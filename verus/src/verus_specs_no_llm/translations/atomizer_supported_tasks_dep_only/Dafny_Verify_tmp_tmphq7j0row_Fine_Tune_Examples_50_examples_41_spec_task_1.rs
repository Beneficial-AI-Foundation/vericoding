// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main(n: int, k: int) -> i :int, j: int
    requires
        n >= 0,
        k == 1 || k >= 0
    ensures
        k + i + j >= 2 * n
;

proof fn lemma_main(n: int, k: int) -> (i: int, j: int)
    requires
        n >= 0,
        k == 1 || k >= 0
    ensures
        k + i + j >= 2 * n
{
    (0, 0)
}

}