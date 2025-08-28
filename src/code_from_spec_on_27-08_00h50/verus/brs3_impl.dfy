use vstd::prelude::*;

verus!{

// <vc-helpers>
// </vc-helpers>
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
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            sum.len() == 1,
            total <= 3 * i,
            total >= 0,
        decreases a.len() - i
    {
        if a[i] <= 3 {
            let contribution = a[i].max(0);
            if total <= i32::MAX - contribution {
                total = total + contribution;
            }
        } else {
            if total <= i32::MAX - 3 {
                total = total + 3;
            }
        }
        i = i + 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}