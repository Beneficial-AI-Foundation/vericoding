use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounded_by_three(a: Seq<i32>, len: int) -> int
    decreases len
{
    if len <= 0 {
        0
    } else {
        let val = if a[len - 1] <= 3 { a[len - 1] } else { 3 };
        sum_bounded_by_three(a, len - 1) + val
    }
}

proof fn sum_bounded_by_three_property(a: Seq<i32>, len: int)
    requires len >= 0, len <= a.len()
    ensures sum_bounded_by_three(a, len) <= 3 * len
    decreases len
{
    if len > 0 {
        sum_bounded_by_three_property(a, len - 1);
    }
}

proof fn sum_bounded_by_three_update(a: Seq<i32>, len: int)
    requires len >= 0, len < a.len()
    ensures 
        sum_bounded_by_three(a, len + 1) == sum_bounded_by_three(a, len) + (if a[len] <= 3 { a[len] } else { 3 })
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
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == N,
            sum.len() == 1,
            N > 0,
            N < 1000,
            total <= 3 * (i as i32),
            total == sum_bounded_by_three(a@, i as int),
            total >= 0,
        decreases a.len() - i
    {
        let old_total = total;
        
        if a[i] <= 3 {
            total = total + a[i];
        } else {
            total = total + 3;
        }
        
        proof {
            sum_bounded_by_three_update(a@, i as int);
            sum_bounded_by_three_property(a@, (i + 1) as int);
            assert(sum_bounded_by_three(a@, (i + 1) as int) <= 3 * ((i + 1) as int));
        }
        
        i = i + 1;
    }
    
    sum.set(0, total);
    // impl-end
}
// </vc-code>

}

fn main() {}