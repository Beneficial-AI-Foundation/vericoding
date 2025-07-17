// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_main(n: int) -> x: int, m: int
    requires
        n > 0
    ensures
        (n <= 0) || (0 <= m && m < n)
;

proof fn lemma_main(n: int) -> (x: int, m: int)
    requires
        n > 0
    ensures
        (n <= 0) || (0 <= m && m < n)
{
    (0, 0)
}

}