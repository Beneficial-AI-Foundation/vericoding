// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Multiply(a: int, b: int) -> result: int
    ensures
        result == a * b
;

proof fn lemma_Multiply(a: int, b: int) -> (result: int)
    ensures
        result == a * b
{
    0
}

}