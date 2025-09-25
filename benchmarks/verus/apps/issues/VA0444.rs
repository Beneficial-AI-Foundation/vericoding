// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: &[int]) -> bool {
    a.len() >= 2 && forall|i: int| 0 <= i < a.len() ==> a[i] >= 1
}

spec fn abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn valid_pair(a: &[int], i: int, j: int) -> bool
    recommends 0 <= i < a.len() && 0 <= j < a.len()
{
    i != j && abs((i+1) - (j+1)) == a[i] + a[j]
}

spec fn count_valid_pairs(a: &[int]) -> int
    recommends valid_input(a)
{
    /* Count of pairs (i,j) where valid_pair(a, i, j) holds */
    0 /* Placeholder for set cardinality */
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: &Vec<i8>) -> (result: i8)
    requires
        a@.len() >= 2,
        forall|i: int| 0 <= i < a@.len() ==> a@[i] >= 1
    ensures
        result >= 0,
        result as int == count_valid_pairs(a@.as_slice())
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}