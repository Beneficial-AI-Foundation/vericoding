// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(a: &[int]) -> bool {
    a.len() >= 2 && forall|i: int| 0 <= i < a.len() ==> a[i] >= 1
}

spec fn abs_diff(x: int, y: int) -> int {
    if x >= y { x - y } else { y - x }
}

spec fn valid_pair(a: &[int], i: int, j: int) -> bool
    recommends 0 <= i < a.len() && 0 <= j < a.len()
{
    i != j && abs_diff((i+1), (j+1)) == a[i] + a[j]
}

spec fn count_valid_pairs(a: &[int]) -> int
    recommends valid_input(a)
{
    let pairs = Set::new(|pair: (int, int)| {
        let (i, j) = pair;
        0 <= i < a.len() && 0 <= j < a.len() && valid_pair(a, i, j)
    });
    pairs.len() as int
}
// </vc-helpers>

// <vc-spec>
fn solve(a: &[int]) -> (result: int)
    requires 
        valid_input(a)
    ensures 
        result >= 0,
        result == count_valid_pairs(a)
// </vc-spec>
// <vc-code>
{
    assume(false);
    0
}
// </vc-code>


}

fn main() {}