use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn bounded_sum(a: Seq<i32>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        a[start] + bounded_sum(a, start + 1, end)
    }
}

proof fn bounded_sum_property(a: Seq<i32>, start: int, end: int)
    requires 
        0 <= start <= end,
        forall|j: int| start <= j < end ==> a[j] <= 3,
    ensures bounded_sum(a, start, end) <= 3 * (end - start)
    decreases end - start
{
    if start >= end {
    } else {
        bounded_sum_property(a, start + 1, end);
    }
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
    let mut total = 0;
    let mut i = 0;
    while i < N
        invariant 
            0 <= i <= N,
            total <= 3 * i,
            i <= a.len(),
        decreases N - i,
    {
        if i < a.len() as i32 {
            let val = if a[i as usize] <= 3 { a[i as usize] } else { 3 };
            total += val;
        } else {
            total += 3;
        }
        i += 1;
    }
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}