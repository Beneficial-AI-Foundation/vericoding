use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_bounded_by_3(a: Seq<i32>, len: int) -> int
    decreases len
{
    if len <= 0 { 0 }
    else { 
        let val = if a[len - 1] > 3 { 3 } else { a[len - 1] };
        sum_bounded_by_3(a, len - 1) + val
    }
}

proof fn sum_bounded_lemma(a: Seq<i32>, len: int)
    requires len >= 0, len <= a.len()
    ensures sum_bounded_by_3(a, len) <= 3 * len
    decreases len
{
    if len <= 0 {
    } else {
        sum_bounded_lemma(a, len - 1);
    }
}

proof fn sum_bounded_step_lemma(a: Seq<i32>, i: int)
    requires i >= 0, i < a.len()
    ensures (
        let val = if a[i] > 3 { 3 } else { a[i] };
        sum_bounded_by_3(a, i + 1) == sum_bounded_by_3(a, i) + val
    )
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
            N > 0,
            N < 1000,
            sum.len() == 1,
            total == sum_bounded_by_3(a@, i as int),
            total <= 3 * (i as i32),
            total >= 0,
            i < 1000,
        decreases a.len() - i,
    {
        proof {
            sum_bounded_step_lemma(a@, i as int);
            sum_bounded_lemma(a@, i as int + 1);
        }
        
        if a[i] > 3 {
            total = total + 3;
        } else {
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