use vstd::prelude::*;

verus!{

// <vc-helpers>
lemma lemma_i32_bounds()
    ensures forall |x: i32, y: i32| x <= 1000 && y <= 3000 ==> #[trigger] (x + y) <= 3100
{
}

lemma lemma_total_bounds(i: i32, total: i32)
    requires 0 <= i < 1000, total <= 3 * i
    ensures total + 3 <= 3 * (i + 1)
{
}
// </vc-helpers>

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
    let mut total = 0i32;
    let mut i = 0i32;
    /* code modified by LLM (iteration 5): added overflow checks and bounds for arithmetic operations */
    while i < N
        invariant
            0 <= i <= N,
            total <= 3 * i,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
            total >= 0,
            total < 3000
        decreases N - i
    {
        if a[i as usize] > 3 {
            proof {
                lemma_total_bounds(i, total);
                assert(total + 3 <= 3 * (i + 1));
                assert(total < 3000);
                assert(total + 3 < 3003);
            }
            total = total + 3;
        } else {
            proof {
                assert(a[i as usize] <= 3);
                assert(total + a[i as usize] <= total + 3);
                lemma_total_bounds(i, total);
                assert(total + 3 <= 3 * (i + 1));
            }
            total = total + a[i as usize];
        }
        i = i + 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}
fn main() {}