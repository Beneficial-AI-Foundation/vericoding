// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MaxSum(x: int, y: int) -> s:int, m:int
    ensures
        s == x+y,
        (m == x || m == y) && x <= m && y <= m
;

proof fn lemma_MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures
        s == x+y,
        (m == x || m == y) && x <= m && y <= m
{
    (0, 0)
}

}