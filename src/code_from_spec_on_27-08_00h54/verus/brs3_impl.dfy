use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn sum_positive_prefix(a: Seq<i32>, len: int) -> int
    decreases len
{
    if len <= 0 {
        0
    } else {
        sum_positive_prefix(a, len - 1) + if a[len - 1] > 0 { a[len - 1] as int } else { 0 }
    }
}

proof fn sum_positive_prefix_bound(a: Seq<i32>, len: int, max_val: i32)
    requires 
        0 <= len <= a.len(),
        forall|j: int| 0 <= j < a.len() ==> #[trigger] a[j] >= 0 && #[trigger] a[j] <= max_val,
    ensures sum_positive_prefix(a, len) <= max_val * len
    decreases len
{
    if len <= 0 {
    } else {
        sum_positive_prefix_bound(a, len - 1, max_val);
        assert(a[len - 1] >= 0);
        assert(a[len - 1] <= max_val);
        if a[len - 1] > 0 {
            assert(sum_positive_prefix(a, len) == sum_positive_prefix(a, len - 1) + a[len - 1]);
            assert(sum_positive_prefix(a, len - 1) <= max_val * (len - 1));
            assert(sum_positive_prefix(a, len) <= max_val * (len - 1) + max_val);
            assert(sum_positive_prefix(a, len) <= max_val * len);
        } else {
            assert(sum_positive_prefix(a, len) == sum_positive_prefix(a, len - 1));
        }
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
    let mut i: i32 = 0;
    while i < N
        invariant
            0 <= i <= N,
            0 <= total <= 3 * i,
            a.len() == N,
            sum.len() == 1,
            N < 1000,
        decreases N - i,
    {
        if a[i as usize] > 0 && total <= 3 * N - a[i as usize] {
            total = total + a[i as usize];
        }
        i += 1;
    }
    sum.set(0, total);
}
// </vc-code>

}

fn main() {}