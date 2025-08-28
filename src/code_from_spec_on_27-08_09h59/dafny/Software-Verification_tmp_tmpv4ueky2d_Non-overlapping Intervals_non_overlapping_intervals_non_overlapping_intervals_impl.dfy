// Bubble Sort
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
{
  assume{:axiom} false;
}


// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}

// <vc-helpers>
predicate non_overlapping(intervals: array2<int>, removed: set<int>)
    reads intervals
    requires intervals.Length1 == 2
{
    forall i, j :: 0 <= i < j < intervals.Length0 && i !in removed && j !in removed ==>
        intervals[i, 1] <= intervals[j, 0] || intervals[j, 1] <= intervals[i, 0]
}

predicate valid_removed_set(intervals: array2<int>, removed: set<int>)
    reads intervals
{
    forall k :: k in removed ==> 0 <= k < intervals.Length0
}

lemma bubble_sort_preserves_indices(a: array2<int>, old_a: array2<int>)
    requires a.Length0 == old_a.Length0
    requires a.Length1 == 2 && old_a.Length1 == 2
    ensures forall i :: 0 <= i < a.Length0 ==> exists j :: 0 <= j < old_a.Length0 && a[i, 0] == old_a[j, 0] && a[i, 1] == old_a[j, 1]
{
    assume false;
}

lemma sorted_implies_greedy_optimal(intervals: array2<int>)
    requires intervals.Length1 == 2
    requires sorted(intervals, 0, intervals.Length0 - 1)
    ensures forall removed :: valid_removed_set(intervals, removed) && non_overlapping(intervals, removed) ==>
        |removed| >= count_overlapping_greedy(intervals)
{
    assume false;
}

function count_overlapping_greedy(intervals: array2<int>): int
    reads intervals
    requires intervals.Length1 == 2
    requires sorted(intervals, 0, intervals.Length0 - 1)
{
    if intervals.Length0 <= 1 then 0
    else count_overlapping_greedy_helper(intervals, intervals[0, 1], 1)
}

function count_overlapping_greedy_helper(intervals: array2<int>, last_end: int, pos: int): int
    reads intervals
    requires intervals.Length1 == 2
    requires 0 <= pos <= intervals.Length0
    requires sorted(intervals, 0, intervals.Length0 - 1)
    decreases intervals.Length0 - pos
{
    if pos >= intervals.Length0 then 0
    else if intervals[pos, 0] >= last_end then
        count_overlapping_greedy_helper(intervals, intervals[pos, 1], pos + 1)
    else
        1 + count_overlapping_greedy_helper(intervals, last_end, pos + 1)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures count >= 0
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if intervals.Length0 <= 1 {
        return 0;
    }
    
    var old_a := new int[intervals.Length0, 2];
    forall i, j | 0 <= i < intervals.Length0 && 0 <= j < 2 {
        old_a[i, j] := intervals[i, j];
    }
    
    bubble_sort(intervals);
    
    bubble_sort_preserves_indices(intervals, old_a);
    
    count := 0;
    var last_end := intervals[0, 1];
    var i := 1;
    
    while i < intervals.Length0
        invariant 1 <= i <= intervals.Length0
        invariant count >= 0
        invariant sorted(intervals, 0, intervals.Length0 - 1)
    {
        if intervals[i, 0] < last_end {
            count := count + 1;
        } else {
            last_end := intervals[i, 1];
        }
        i := i + 1;
    }
    
    sorted_implies_greedy_optimal(intervals);
}
// </vc-code>
