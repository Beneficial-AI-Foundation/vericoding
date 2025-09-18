// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed bounds checking for negative indices and large vectors */
spec fn sum_range(y: &Vec<i32>, start: int, end: int) -> int {
    if start > end || start < 0 || end < 0 || end >= y@.len() {
        0
    } else {
        y.view().subrange(start as usize, (end+1) as usize).sum()
    }
}
// </vc-helpers>

// <vc-spec>
fn trapezoid(y: Vec<i32>, dx: i32) -> (result: i32)
    requires 
        y.len() > 0,
        dx > 0,
    ensures
        (forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] == y[0]) ==> 
            result == dx * (y.len() - 1) as i32 * y[0],
        (forall|i: int| 0 <= i < y.len() ==> #[trigger] y[i] >= 0) ==> result >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed while loop condition by adding parentheses */
{
    let n = y.len();
    if n == 1 {
        0
    } else {
        let mut inner_sum = 0;
        let mut i = 1;
        while (i < n - 1)
            invariant 1 <= i,
            invariant i <= n - 1,
            invariant inner_sum == sum_range(&y, 1, i - 1)
        {
            inner_sum += y[i];
            i += 1;
        }
        let total = y[0] + y[n-1] + 2 * inner_sum;
        (dx * total) / 2
    }
}
// </vc-code>

}
fn main() {}