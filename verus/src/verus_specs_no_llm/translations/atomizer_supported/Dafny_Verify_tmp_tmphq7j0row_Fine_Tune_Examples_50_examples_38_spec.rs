// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main(n: int) -> i: int, x: int, y:int
    requires
        n >= 0
    ensures
        (i % 2 != 0) || (x == 2 * y)
;

proof fn lemma_main(n: int) -> (i: int, x: int, y: int)
    requires
        n >= 0
    ensures
        (i % 2 != 0) || (x == 2 * y)
{
    (0, 0, 0)
}

}