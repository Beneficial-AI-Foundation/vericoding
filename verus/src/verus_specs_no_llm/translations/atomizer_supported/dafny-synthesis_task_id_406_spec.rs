// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsOdd(n: int) -> result: bool
    ensures
        result <==> n % 2 == 1
;

proof fn lemma_IsOdd(n: int) -> (result: bool)
    ensures
        result <==> n % 2 == 1
{
    false
}

}