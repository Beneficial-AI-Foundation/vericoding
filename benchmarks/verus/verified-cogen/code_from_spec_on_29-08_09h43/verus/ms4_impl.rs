use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounds_helper(a: &Vec<i32>, n: int, bound: int) -> bool {
    forall |i: int| 0 <= i < n ==> a@[i] <= bound
}

proof fn arithmetic_bounds_lemma(x: i32, y: i32, bound: i32)
    requires
        x <= bound,
        y <= bound,
        bound < 1000,
    ensures
        x + y <= 2 * bound,
{
}
// </vc-helpers>

// <vc-description>
/*

*/
// </vc-description>

// <vc-spec>
fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32) 
	// pre-conditions-start
	requires 
		old(a).len() == N,
		old(sum).len() == 1,
		N > 0,
		N < 1000,
	// pre-conditions-end
	// post-conditions-start
	ensures
		sum[0] <= 3 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    /* code modified by LLM (iteration 5): added explicit type annotations and overflow prevention with bounds checking */
    while i < N
        invariant
            0 <= i <= N,
            total <= 3 * N,
            N == old(a).len(),
            a.len() == N,
            N < 1000,
            total >= 0,
        decreases N - i
    {
        if a[i as usize] > 0 {
            /* code modified by LLM (iteration 5): check bounds before addition to prevent overflow */
            if total <= 3 * N - a[i as usize] {
                total += a[i as usize];
            } else {
                total = 3 * N;
                break;
            }
        }
        i += 1;
    }
    sum[0] = total;
    // impl-end
}
// </vc-code>

}
fn main() {}