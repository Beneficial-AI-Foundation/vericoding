// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_non_overlapping_intervals(intervals: array2<int>) -> count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures count >= 0
{
}



// Bubble Sort
// SPEC 


// Bubble Sort
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1
    requires
        1 <= intervals.Length0 <= 100000,
        intervals.Length1 == 2,
        forall |i: int| 0 <= i < intervals.Length0 ==> -50000 <= intervals.index(i, 0) <= 50000,
        forall |i: int| 0 <= i < intervals.Length0 ==> -50000 <= intervals.index(i, 1) <= 50000
    // TODO: modify the,
        a.Length1 == 2
    ensures
        clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.,
        count >= 0,
        sorted(a, 0, a.Length0 - 1)
;

proof fn lemma_non_overlapping_intervals(intervals: array2<int>) -> (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i: : 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures count >= 0
{
}



// Bubble Sort
// SPEC 


// Bubble Sort
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
    requires
        1 <= intervals.Length0 <= 100000,
        intervals.Length1 == 2,
        forall |i: int| 0 <= i < intervals.Length0 ==> -50000 <= intervals.index(i, 0) <= 50000,
        forall |i: int| 0 <= i < intervals.Length0 ==> -50000 <= intervals.index(i, 1) <= 50000
    // TODO: modify the,
        a.Length1 == 2
    ensures
        clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.,
        count >= 0,
        sorted(a, 0, a.Length0 - 1)
{
    (0, 0, 0, 0, 0)
}

}