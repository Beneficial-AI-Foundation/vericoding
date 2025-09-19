// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, seq: Vec<usize>) -> (result: (usize, usize))
    requires 
        n > 0,
        seq.len() == n,
    ensures
        (result.0 == 0 && result.1 == 0) || (1 <= result.0 < result.1 <= n),
{
    // impl-start
    assume(false);
    (0, 0)
    // impl-end
}

fn is_valid_after_reverse(seq: Vec<usize>, l: usize, r: usize) -> (result: bool)
    requires 
        seq.len() > 0,
        l > 0,
        r <= seq.len(),
        l < r,
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // let result = solve(8, vec![1, 6, 5, 4, 3, 2, 7, 8]);
    // println!("{:?}", result);
    // 
    // let result2 = solve(4, vec![1, 2, 3, 4]);
    // println!("{:?}", result2);
    // 
    // let result3 = solve(3, vec![3, 2, 1]);
    // println!("{:?}", result3);
}