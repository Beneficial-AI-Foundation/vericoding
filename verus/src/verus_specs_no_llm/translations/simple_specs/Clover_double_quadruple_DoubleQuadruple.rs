// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_DoubleQuadruple(x: int) -> a: int, b: int
    ensures
        a == 2 * x && b == 4 * x
;

proof fn lemma_DoubleQuadruple(x: int) -> (a: int, b: int)
    ensures
        a == 2 * x && b == 4 * x
{
    (0, 0)
}

}