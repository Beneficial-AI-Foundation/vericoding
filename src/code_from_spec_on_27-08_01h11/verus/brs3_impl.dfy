use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounded_by_3(a: Seq<i32>, len: int) -> int
    decreases len
{
    if len <= 0 {
        0
    } else {
        let val = if a[len - 1] > 3 { 3 } else { a[len - 1] };
        val + sum_bounded_by_3(a, len - 1)
    }
}

proof fn sum_bounded_by_3_property(a: Seq<i32>, len: int)
    requires len >= 0
    ensures sum_bounded_by_3(a, len) <= 3 * len
    decreases len
{
    if len <= 0 {
    } else {
        sum_bounded_by_3_property(a, len - 1);
    }
}

proof fn sum_step_property(total: i32, val: i32, i: i32)
    requires 
        total <= 3 * i,
        val <= 3,
        i >= 0,
        total >= 0,
        i < 1000
    ensures total + val <= 3 * (i + 1)
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
    let mut total: i32 = 0;
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            total <= 3 * i,
            a.len() == N,
            sum.len() == 1,
            i >= 0,
            N >= 0,
            N < 1000,
            total >= 0,
            total <= 3000,
        decreases N - i,
    {
        let val = if a[i as usize] > 3 { 3 } else { a[i as usize] };
        
        proof {
            sum_step_property(total, val, i);
        }
        
        total = total + val;
        i = i + 1;
    }
    sum.set(0, total);
}
// </vc-code>

}

fn main() {}