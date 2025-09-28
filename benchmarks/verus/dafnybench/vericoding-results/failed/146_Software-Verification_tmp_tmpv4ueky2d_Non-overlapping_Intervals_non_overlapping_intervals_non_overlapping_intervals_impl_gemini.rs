// <vc-preamble>
use vstd::prelude::*;

verus! {

fn bubble_sort(a: &mut Vec<Vec<i32>>)
    requires
        old(a).len() >= 1,
        forall|i: int| 0 <= i < old(a).len() ==> #[trigger] old(a)[i].len() == 2,
    ensures
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == 2,
        sorted(a, 0, (a.len() - 1) as int),
{
    assume(false);
}

spec fn sorted(a: &Vec<Vec<i32>>, l: int, u: int) -> bool
    recommends
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].len() == 2,
{
    forall|i: int, j: int| 0 <= l <= i <= j <= u < a.len() ==> #[trigger] a[i][1] <= #[trigger] a[j][1]
}

spec fn partitioned(a: &Vec<Vec<i32>>, i: int) -> bool
    recommends
        forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k].len() == 2,
{
    forall|k: int, k_prime: int| 0 <= k <= i < k_prime < a.len() ==> #[trigger] a[k][1] <= #[trigger] a[k_prime][1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes required */
proof fn lemma_sorted_get(a: &Vec<Vec<i32>>, l: int, u: int, i: int, j: int)
    requires
        0 <= l,
        u < a.len(),
        sorted(a, l, u),
        l <= i <= j <= u,
        forall|k: int| 0 <= k < a.len() ==> #[trigger] a[k].len() == 2,
    ensures
        a[i][1] <= a[j][1],
{
}
// </vc-helpers>

// <vc-spec>
fn non_overlapping_intervals(intervals: &mut Vec<Vec<i32>>) -> (count: i32)
    requires
        1 <= old(intervals).len() <= 100000,
        forall|i: int| 0 <= i < old(intervals).len() ==> #[trigger] old(intervals)[i].len() == 2,
        forall|i: int| 0 <= i < old(intervals).len() ==> -50000 <= #[trigger] old(intervals)[i][0] <= 50000,
        forall|i: int| 0 <= i < old(intervals).len() ==> -50000 <= #[trigger] old(intervals)[i][1] <= 50000,

    ensures
        count >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): handled empty case and added bounds checks */
    bubble_sort(intervals);
    let n = intervals.len();
    if n == 0 {
        // This path is unreachable due to the requires clause, but helps the verifier
        return 0;
    }

    assert(n <= 100000);
    assert(sorted(intervals, 0, (n - 1) as int));
    assert(forall|k: int| 0 <= k < n ==> #[trigger] intervals[k].len() == 2);

    let mut count: i32 = 1;
    let mut last_end = intervals[0][1];

    let mut i: usize = 1;
    while i < n
        invariant
            n == intervals.len(),
            1 <= i <= n,
            1 <= n <= 100000,
            sorted(intervals, 0, (n - 1) as int),
            forall|k: int| 0 <= k < n ==> #[trigger] intervals[k].len() == 2,
            count >= 1,
            count <= i as int,
        decreases n - i
    {
        if intervals[i][0] >= last_end {
            count = count + 1;
            last_end = intervals[i][1];
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}