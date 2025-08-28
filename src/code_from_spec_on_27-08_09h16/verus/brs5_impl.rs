use vstd::prelude::*;

verus!{

// <vc-helpers>
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
		sum[0] <= 5 * N,
	// post-conditions-end
// </vc-spec>

// <vc-code>
{
    // impl-start
    let mut total: i32 = 0;
    let mut i: usize = 0;
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
        let value = if a[i] <= 5 { a[i] } else { 5 };
        let old_total = total;
        total = total + value;
        proof {
            assert(value >= 0 && value <= 5);
            assert(total >= old_total);
        }
        i = i + 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}