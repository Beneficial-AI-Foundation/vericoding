// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main(n: int, k: int) -> k_out: int
    requires
        n > 0,
        k > n
    ensures
        k_out >= 0
;

proof fn lemma_main(n: int, k: int) -> (k_out: int)
    requires
        n > 0,
        k > n
    ensures
        k_out >= 0
{
    0
}

}