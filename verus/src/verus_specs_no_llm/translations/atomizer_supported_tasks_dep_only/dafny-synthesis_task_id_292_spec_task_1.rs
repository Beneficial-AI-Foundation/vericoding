// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Quotient(a: int, b: int) -> result: int
    requires
        b != 0
    ensures
        result == a / b
;

proof fn lemma_Quotient(a: int, b: int) -> (result: int)
    requires
        b != 0
    ensures
        result == a / b
{
    0
}

}