// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_LastDigit(n: int) -> d: int
    requires
        n >= 0
    ensures
        0 <= d < 10,
        n % 10 == d
;

proof fn lemma_LastDigit(n: int) -> (d: int)
    requires
        n >= 0
    ensures
        0 <= d < 10,
        n % 10 == d
{
    0
}

}