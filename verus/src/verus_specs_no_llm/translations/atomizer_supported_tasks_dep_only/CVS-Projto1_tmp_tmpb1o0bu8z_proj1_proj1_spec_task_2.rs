// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int
reads a
    requires
        0 <= i <= j <= a.len()
{
    0
}

spec fn spec_queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> r:int
    requires
        is_prefix_sum_for(a,c) && 0 <= i <= j <= a.len() < c.len()
    ensures
        r == sum(a, i,j)
;

proof fn lemma_queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        is_prefix_sum_for(a,c) && 0 <= i <= j <= a.len() < c.len()
    ensures
        r == sum(a, i,j)
{
    0
}

}