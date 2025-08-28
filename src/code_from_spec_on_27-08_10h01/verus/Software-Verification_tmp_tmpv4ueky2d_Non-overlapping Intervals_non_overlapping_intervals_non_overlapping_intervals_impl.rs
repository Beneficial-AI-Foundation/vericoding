use vstd::prelude::*;

verus! {

// Bubble Sort
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


// Predicates for Bubble Sort
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

// <vc-helpers>
spec fn overlaps(a: &Vec<i32>, b: &Vec<i32>) -> bool
    recommends
        a.len() == 2,
        b.len() == 2,
{
    a[0] < b[1] && b[0] < a[1]
}

spec fn has_overlapping_intervals(intervals: &Vec<Vec<i32>>) -> bool
    recommends
        forall|i: int| 0 <= i < intervals.len() ==> #[trigger] intervals[i].len() == 2,
{
    exists|i: int, j: int| 0 <= i < j < intervals.len() && overlaps(&intervals[i], &intervals[j])
}

spec fn count_overlapping_pairs(intervals: &Vec<Vec<i32>>) -> int
    recommends
        forall|i: int| 0 <= i < intervals.len() ==> #[trigger] intervals[i].len() == 2,
{
    count_overlapping_pairs_rec(intervals, 0)
}

spec fn count_overlapping_pairs_rec(intervals: &Vec<Vec<i32>>, start: int) -> int
    recommends
        forall|i: int| 0 <= i < intervals.len() ==> #[trigger] intervals[i].len() == 2,
    decreases intervals.len() - start
{
    if start >= intervals.len() {
        0
    } else {
        count_overlaps_with_index(intervals, start, start + 1) + count_overlapping_pairs_rec(intervals, start + 1)
    }
}

spec fn count_overlaps_with_index(intervals: &Vec<Vec<i32>>, idx: int, start: int) -> int
    recommends
        forall|i: int| 0 <= i < intervals.len() ==> #[trigger] intervals[i].len() == 2,
    decreases intervals.len() - start
{
    if start >= intervals.len() || idx >= intervals.len() || idx < 0 {
        0
    } else {
        (if overlaps(&intervals[idx], &intervals[start]) { 1 } else { 0 }) + count_overlaps_with_index(intervals, idx, start + 1)
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn non_overlapping_intervals(intervals: &mut Vec<Vec<i32>>) -> (count: i32)
    requires
        1 <= old(intervals).len() <= 100000,
        forall|i: int| 0 <= i < old(intervals).len() ==> #[trigger] old(intervals)[i].len() == 2,
        forall|i: int| 0 <= i < old(intervals).len() ==> -50000 <= #[trigger] old(intervals)[i][0] <= 50000,
        forall|i: int| 0 <= i < old(intervals).len() ==> -50000 <= #[trigger] old(intervals)[i][1] <= 50000,
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures
        count >= 0,
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    bubble_sort(intervals);
    
    let mut count = 0i32;
    let mut i = 0usize;
    
    while i < intervals.len()
        invariant
            0 <= i <= intervals.len(),
            count >= 0,
            intervals.len() >= 1,
            forall|j: int| 0 <= j < intervals.len() ==> #[trigger] intervals[j].len() == 2,
            sorted(intervals, 0, (intervals.len() - 1) as int),
    {
        if i > 0 {
            let prev_end = intervals[i - 1][1];
            let curr_start = intervals[i][0];
            
            if prev_end > curr_start {
                count = count + 1;
            }
        }
        i = i + 1;
    }
    
    count
}
// </vc-code>

fn main() {
}

}