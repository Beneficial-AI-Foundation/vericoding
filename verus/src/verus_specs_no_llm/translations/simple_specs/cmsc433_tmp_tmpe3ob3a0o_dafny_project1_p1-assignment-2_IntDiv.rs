// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IntDiv(m: int, n: int) -> d : int, r : int
    requires
        n > 0
    ensures
        m == n * d + r && 0 <= r < n // TODO
;

proof fn lemma_IntDiv(m: int, n: int) -> (d: int, r: int)
    requires
        n > 0
    ensures
        m == n * d + r && 0 <= r < n // TODO
{
    (0, 0)
}

}