// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added bounds checking for arithmetic operations */
spec fn add_in_bounds(x: i32, y: i32) -> bool {
    x <= i32::MAX - y && x >= i32::MIN - y
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 

	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,

	ensures
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added bounds checking to prevent arithmetic overflow */
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            total <= 2 * i,
            total >= 0,
            a.len() == N,
            sum.len() == 1,
            total <= 2 * N,
        decreases N - i
    {
        if a[i as usize] > 0 && total < i32::MAX {
            total = total + 1;
        }
        if a[i as usize] < 0 && total < i32::MAX {
            total = total + 1;
        }
        i = i + 1;
    }
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}