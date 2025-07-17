// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ComputeIsEven(x: int) -> is_even:bool
    ensures
        (x % 2 == 0)==is_even
;

proof fn lemma_ComputeIsEven(x: int) -> (is_even: bool)
    ensures
        (x % 2 == 0)==is_even
{
    false
}

}