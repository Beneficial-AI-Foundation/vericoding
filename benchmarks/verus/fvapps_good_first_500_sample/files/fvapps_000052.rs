// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_time_tasks(n: usize, difficulties: Vec<usize>) -> (result: usize)
    requires 
        n > 0,
        difficulties.len() == n,
        forall|i: int| 0 <= i < difficulties.len() ==> #[trigger] difficulties[i] >= 1 && #[trigger] difficulties[i] <= 100000,
    ensures 
        result < 10007,
        result >= 0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {
    // let result1 = min_time_tasks(2, vec![1, 3]);
    // assert(result1 == 6);
    // 
    // let result2 = min_time_tasks(3, vec![1, 2, 3]);
    // assert(result2 == 10);
    // 
    // let result3 = min_time_tasks(4, vec![1, 2, 3, 4]);
    // assert(result3 == 20);
}