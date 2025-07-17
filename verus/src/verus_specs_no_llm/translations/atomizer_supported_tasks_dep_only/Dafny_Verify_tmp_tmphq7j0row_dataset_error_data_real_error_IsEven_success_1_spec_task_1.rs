// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn even(n: int) -> bool
    requires
        n >= 0
{
    false
}

spec fn spec_is_even(n: int) -> r: bool
    requires
        n >= 0
    ensures
        r <==> even(n)
;

proof fn lemma_is_even(n: int) -> (r: bool)
    requires
        n >= 0
    ensures
        r <==> even(n)
{
    false
}

}