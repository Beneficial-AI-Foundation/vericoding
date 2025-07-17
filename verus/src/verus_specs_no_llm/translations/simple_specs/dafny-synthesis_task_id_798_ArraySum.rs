// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sumTo(a: Vec<int>, n: int) -> int
    requires
        a != null,
        0 <= n && n <= a.len()
 reads a
{
    0
}

spec fn spec_ArraySum(a: Vec<int>) -> result: int
    ensures
        result == sumTo(a, a.len())
;

proof fn lemma_ArraySum(a: Vec<int>) -> (result: int)
    ensures
        result == sumTo(a, a.len())
{
    0
}

}