// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main(n: int) -> a: int, b: int
    requires
        n >= 0
    ensures
        a + b == 3 * n
;

proof fn lemma_main(n: int) -> (a: int, b: int)
    requires
        n >= 0
    ensures
        a + b == 3 * n
{
    (0, 0)
}

}