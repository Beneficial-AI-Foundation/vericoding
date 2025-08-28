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

proof fn sum_bounded_invariant(a: Seq<i32>, len: int)
    requires len >= 0, len <= a.len()
    ensures sum_bounded_by_three(a, len) <= 3 * len
    decreases len
{
    if len <= 0 {
        assert(sum_bounded_by_three(a, len) == 0);
        assert(3 * len <= 0);
    } else {
        sum_bounded_invariant(a, len - 1);
        let val = if a[len - 1] <= 3 { a[len - 1] } else { 3 };
        assert(val <= 3);
        assert(sum_bounded_by_three(a, len) == sum_bounded_by_three(a, len - 1) + val);
        assert(sum_bounded_by_three(a, len - 1) + val <= 3 * (len - 1) + 3);
        assert(3 * (len - 1) + 3 == 3 * len);
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
            -3000 <= total <= 3000,
        decreases a.len() - i
    {
        proof {
            sum_bounded_invariant(a@, i as int);
            assert(i < a.len());
            assert((i as int) < a@.len());
        }
        
        let old_total = total;
        if a[i] <= 3 {
            total = total + a[i];
        } else {
            total = total + 3;
        }
        
        proof {
            let val = if a[i] <= 3 { a[i] } else { 3 };
            assert(total == old_total + val);
            assert(val <= 3);
            assert(old_total <= 3 * (i as i32));
            assert(total <= 3 * (i as i32) + 3);
            assert(total <= 3 * ((i + 1) as i32));
            assert(total == sum_bounded_by_three(a@, (i + 1) as int));
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == a.len());
        assert(total <= 3 * (a.len() as i32));
        assert(a.len() == N);
        assert(total <= 3 * N);
    }
    
    sum.set(0, total);
}
// </vc-code>

}
fn main() {}