// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main() -> t1: int, t2: int, x: int, y: int
    ensures
        y >= 1
;

proof fn lemma_main() -> (t1: int, t2: int, x: int, y: int)
    ensures
        y >= 1
{
    (0, 0, 0, 0)
}

}