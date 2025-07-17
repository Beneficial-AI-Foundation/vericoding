// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsEven(n: int) -> result: bool
    ensures
        result <==> n % 2 == 0
;

proof fn lemma_IsEven(n: int) -> (result: bool)
    ensures
        result <==> n % 2 == 0
{
    false
}

}