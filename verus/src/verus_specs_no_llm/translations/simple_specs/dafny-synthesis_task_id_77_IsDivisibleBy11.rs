// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IsDivisibleBy11(n: int) -> result: bool
    ensures
        result <==> n % 11 == 0
;

proof fn lemma_IsDivisibleBy11(n: int) -> (result: bool)
    ensures
        result <==> n % 11 == 0
{
    false
}

}