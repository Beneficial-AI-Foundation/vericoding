// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn countTo(a: Vec<bool>, n: int) -> int
    requires
        a != null,
        0 <= n && n <= a.len()
 reads a
{
    0
}

spec fn spec_CountTrue(a: Vec<bool>) -> result: int
    requires
        a != null
    ensures
        result == countTo(a, a.len())
;

proof fn lemma_CountTrue(a: Vec<bool>) -> (result: int)
    requires
        a != null
    ensures
        result == countTo(a, a.len())
{
    0
}

}