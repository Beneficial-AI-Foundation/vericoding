// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn sum(a: Vec<int>, i: int, j: int) -> int
    requires
        0 <= i <= j <= a.len()
  reads a
{
    0
}

spec fn spec_queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> r: int
    requires
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a,c)
    ensures
        r == sum(a, i, j)
;

proof fn lemma_queryFast(a: Vec<int>, c: Vec<int>, i: int, j: int) -> (r: int)
    requires
        0 <= i <= j <= a.len(),
        is_prefix_sum_for(a,c)
    ensures
        r == sum(a, i, j)
{
    0
}

}