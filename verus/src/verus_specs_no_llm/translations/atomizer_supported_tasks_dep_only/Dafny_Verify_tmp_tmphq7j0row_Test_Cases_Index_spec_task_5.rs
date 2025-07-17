// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_MaxSum(x: int, y: int) -> s: int, m: int
    ensures
        s == x + y,
        m == if x >= y then x else y
;

proof fn lemma_MaxSum(x: int, y: int) -> (s: int, m: int)
    ensures
        s == x + y,
        m == if x >= y then x else y
{
    (0, 0)
}

}