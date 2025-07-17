// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_HasOppositeSign(a: int, b: int) -> result: bool
    ensures
        result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
;

proof fn lemma_HasOppositeSign(a: int, b: int) -> (result: bool)
    ensures
        result <==> (a < 0 && b > 0) || (a > 0 && b < 0)
{
    false
}

}