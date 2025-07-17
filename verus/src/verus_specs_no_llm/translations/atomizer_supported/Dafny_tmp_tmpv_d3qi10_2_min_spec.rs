// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn min(a: int, b: int) -> int
    ensures
        min(a, b) <= a && min(a, b) <= b,
        min(a, b) == a || min(a, b) == b
{
    0
}

spec fn spec_minMethod(a: int, b: int) -> c: int
    ensures
        c <= a && c <= b,
        c == a || c == b
    // Ou encore:,
        c == min(a, b)
;

proof fn lemma_minMethod(a: int, b: int) -> (c: int)
    ensures
        c <= a && c <= b,
        c == a || c == b
    // Ou encore:,
        c == min(a, b)
{
    0
}

}