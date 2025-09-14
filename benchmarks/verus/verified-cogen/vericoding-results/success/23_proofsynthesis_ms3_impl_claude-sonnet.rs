// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added overflow prevention helper */
spec fn safe_add(a: i32, b: i32) -> bool {
    a >= 0 && b >= 0 && a <= i32::MAX - b
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
    /* code modified by LLM (iteration 3): fixed overflow and invariant preservation */
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            sum.len() == 1,
            total >= 0,
            total <= 2 * (i as i32),
        decreases a.len() - i
    {
        if a[i] <= 2 && a[i] >= 0 && total <= i32::MAX - a[i] {
            total = total + a[i];
        }
        i = i + 1;
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}