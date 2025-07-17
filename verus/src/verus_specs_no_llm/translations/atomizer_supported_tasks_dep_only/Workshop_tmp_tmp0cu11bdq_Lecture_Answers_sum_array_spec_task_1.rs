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
{
    0
}

spec fn spec_sum_array(a: Vec<int>) -> sum: int
    requires
        a != null
    ensures
        sum == sumTo(a, a.len())
;

proof fn lemma_sum_array(a: Vec<int>) -> (sum: int)
    requires
        a != null
    ensures
        sum == sumTo(a, a.len())
{
    0
}

}