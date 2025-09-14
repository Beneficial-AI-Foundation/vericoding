// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): add overflow bounds checking */
spec fn safe_add(x: i32, y: i32) -> bool {
    x <= i32::MAX - y && x >= i32::MIN - y
}
// </vc-helpers>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)

	requires
		N > 0,
		old(a).len() == N,
		old(b).len() == N,
		old(sum).len() == 1,
        N < 1000,

	ensures
		sum[0] <= 2 * N,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix arithmetic overflow by using bounds checking */
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            0 <= total <= 2 * i,
            total <= 2 * N,
            a.len() == N,
            b.len() == N,
            sum.len() == 1,
        decreases N - i
    {
        if a[i as usize] > b[i as usize] {
            if total < i32::MAX {
                total = total + 1;
            }
        } else {
            if total < i32::MAX {
                total = total + 1;
            }
        }
        i = i + 1;
    }
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}