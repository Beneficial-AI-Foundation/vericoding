use vstd::prelude::*;

verus!{

// <vc-helpers>
fn lemma_bounded_sum(total: i32, ai: i32, i: i32)
    requires
        total <= 5 * i,
        ai <= 5,
        i < 1000,
        total >= 0,
    ensures
        total + ai <= 5 * (i + 1)
{
    assert(total + ai <= 5 * i + 5);
    assert(5 * i + 5 == 5 * (i + 1));
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
		sum[0] <= 5 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total: i32 = 0;
    let mut i: usize = 0;
    /* code modified by LLM (iteration 5): fixed type conversion for lemma call */
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            total <= 5 * (i as i32),
            total >= 0,
        decreases a.len() - i
    {
        if a[i] <= 5 {
            proof {
                lemma_bounded_sum(total, a@[i as int], i as i32);
            }
            total = total + a[i];
        }
        i = i + 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}