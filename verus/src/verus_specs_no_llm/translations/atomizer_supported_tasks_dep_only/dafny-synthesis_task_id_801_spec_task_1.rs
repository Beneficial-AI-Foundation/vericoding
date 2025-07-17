// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountEqualNumbers(a: int, b: int, c: int) -> count: int
    ensures
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) | (a != b && b == c) .len()| (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c)
;

proof fn lemma_CountEqualNumbers(a: int, b: int, c: int) -> (count: int)
    ensures
        count >= 0 && count <= 3,
        (count == 3) <==> (a == b && b == c),
        (count == 2) <==> ((a == b && b != c) | (a != b && b == c) .len()| (a == c && b != c)),
        (count == 1) <==> (a != b && b != c && a != c)
{
    0
}

}