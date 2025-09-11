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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}