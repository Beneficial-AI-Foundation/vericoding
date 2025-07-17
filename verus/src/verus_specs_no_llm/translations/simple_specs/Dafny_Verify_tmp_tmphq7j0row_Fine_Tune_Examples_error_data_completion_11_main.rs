// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main(x: int) -> j :int, i :int
    requires
        x > 0
    ensures
        j == 2 * x
;

proof fn lemma_main(x: int) -> (j: int, i: int)
    requires
        x > 0
    ensures
        j == 2 * x
{
    (0, 0)
}

}