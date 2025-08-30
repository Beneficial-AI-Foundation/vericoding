// IMPL 
method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures count >= 0
{
    if intervals.Length0 <= 1 {
        count := 0;
        return;
    }
    
    // Sort intervals by end time to use greedy approach
    bubble_sort(intervals);
    
    var removals := 0;
    var lastEnd := intervals[0, 1];
    
    var i := 1;
    while i < intervals.Length0
        invariant 1 <= i <= intervals.Length0
        invariant removals >= 0
        invariant sorted(intervals, 0, intervals.Length0 - 1)
    {
        if intervals[i, 0] < lastEnd {
            // Overlapping interval, need to remove it
            removals := removals + 1;
        } else {
            // Non-overlapping, update lastEnd
            lastEnd := intervals[i, 1];
        }
        i := i + 1;
    }
    
    count := removals;
}

// IMPL 
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
{
    if a.Length0 <= 1 {
        return;
    }
    
    var i := 0;
    while i < a.Length0
        invariant 0 <= i <= a.Length0
        invariant partitioned(a, i - 1)
        invariant sorted(a, 0, i - 1)
    {
        var j := a.Length0 - 1;
        while j > i
            invariant i <= j < a.Length0
            invariant partitioned(a, i - 1)
            invariant sorted(a, 0, i - 1)
            invariant forall k :: j < k < a.Length0 ==> a[j, 1] <= a[k, 1]
        {
            if a[j - 1, 1] > a[j, 1] {
                // Swap elements
                var temp0 := a[j - 1, 0];
                var temp1 := a[j - 1, 1];
                a[j - 1, 0] := a[j, 0];
                a[j - 1, 1] := a[j, 1];
                a[j, 0] := temp0;
                a[j, 1] := temp1;
            }
            j := j - 1;
        }
        i := i + 1;
    }
}

// ATOM 
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

// ATOM 
predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}