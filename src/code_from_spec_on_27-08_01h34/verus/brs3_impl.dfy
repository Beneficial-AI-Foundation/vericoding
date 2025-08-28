use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounded_at_3(a: Seq<i32>, end: int) -> int
    decreases end
{
    if end <= 0 {
        0
    } else {
        let val = if a[end - 1] <= 3 { a[end - 1] } else { 3 };
        sum_bounded_at_3(a, end - 1) + val
    }
}

proof fn sum_bounded_at_3_property(a: Seq<i32>, end: int)
    requires 0 <= end <= a.len()
    ensures sum_bounded_at_3(a, end) <= 3 * end
    decreases end
{
    if end > 0 {
        sum_bounded_at_3_property(a, end - 1);
    }
}

proof fn sum_bounded_at_3_step(a: Seq<i32>, i: int)
    requires 0 <= i < a.len()
    ensures sum_bounded_at_3(a, i + 1) == sum_bounded_at_3(a, i) + (if a[i] <= 3 { a[i] } else { 3 })
{
}

proof fn sum_bounded_at_3_bounds(a: Seq<i32>, i: int)
    requires 0 <= i <= a.len() <= 1000
    ensures -3000 <= sum_bounded_at_3(a, i) <= 3 * i
    decreases i
{
    if i > 0 {
        sum_bounded_at_3_bounds(a, i - 1);
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
    let mut total = 0i32;
    let mut i = 0usize;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            total == sum_bounded_at_3(a@, i as int),
            -3000 <= total <= 3 * (i as i32),
        decreases a.len() - i,
    {
        proof {
            sum_bounded_at_3_step(a@, i as int);
            sum_bounded_at_3_bounds(a@, (i + 1) as int);
        }
        if a[i] <= 3 {
            total = total + a[i];
        } else {
            total = total + 3;
        }
        i = i + 1;
    }
    
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}