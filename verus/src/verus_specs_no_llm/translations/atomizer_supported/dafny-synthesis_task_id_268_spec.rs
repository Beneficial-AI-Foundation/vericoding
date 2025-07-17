// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_StarNumber(n: int) -> star: int
    requires
        n >= 0
    ensures
        star == 6 * n * (n - 1) + 1
;

proof fn lemma_StarNumber(n: int) -> (star: int)
    requires
        n >= 0
    ensures
        star == 6 * n * (n - 1) + 1
{
    0
}

}