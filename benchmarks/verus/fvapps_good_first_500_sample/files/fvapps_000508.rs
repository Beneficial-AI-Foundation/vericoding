// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_well_bracketed_sum(n: usize, k: usize, values: Vec<i64>, brackets: Vec<usize>) -> (result: i64)
    requires 
        values.len() == n,
        brackets.len() == n,
        k >= 1,
    ensures
        n == 1 ==> result == 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result = solve_well_bracketed_sum(6, 3, vec![4, 5, -2, 1, 1, 6], vec![1, 3, 4, 2, 5, 6]);
    // println!("{}", result);
}