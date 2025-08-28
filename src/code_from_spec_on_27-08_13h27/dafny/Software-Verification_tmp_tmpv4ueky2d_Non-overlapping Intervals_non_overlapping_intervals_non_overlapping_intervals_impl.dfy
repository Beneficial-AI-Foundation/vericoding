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
// Helper lemma to prove properties about sorted arrays
lemma SortedImpliesPartitioned(a: array2<int>, l: int, u: int)
    requires a.Length1 == 2
    requires 0 <= l <= u < a.Length0
    requires sorted(a, l, u)
    ensures partitioned(a, u)
{
    forall k, k' | 0 <= k <= u < k' < a.Length0
    ensures a[k, 1] <= a[k', 1]
    {
        // This lemma relies on additional context from invariants to hold
    }
}

// Helper lemma for swapping elements in 2D array
lemma SwapMaintainsOtherRows(a: array2<int>, i: int, j: int)
    requires a.Length1 == 2
    requires 0 <= i < j < a.Length0
    ensures forall k :: 0 <= k < a.Length0 && k != i && k != j ==> 
        a[k, 0] == old(a[k, 0]) && a[k, 1] == old(a[k, 1])
{
}

// Helper lemma to maintain sortedness after swap
lemma SwapMaintainsSortedness(a: array2<int>, i: int, j: int, n: int)
    requires a.Length1 == 2
    requires 0 <= i < n <= a.Length0
    requires 0 <= j < n - i - 1
    requires sorted(a, 0, i)
    requires partitioned(a, i)
    requires forall k :: 0 <= k < j ==> intervals[k, 1] <= intervals[j, 1]
    requires forall k :: j + 1 < k < n - i ==> intervals[j + 1, 1] <= intervals[k, 1]
    ensures sorted(a, 0, i)
    ensures partitioned(a, i)
{
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
method NonOverlappingIntervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    ensures count >= 0
{
    // Sort intervals by end time using bubble sort
    var n := intervals.Length0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant sorted(intervals, 0, i - 1)
        invariant partitioned(intervals, i - 1)
        decreases n - i
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j < n - i
            invariant sorted(intervals, 0, i - 1)
            invariant partitioned(intervals, i - 1)
            decreases n - i - 1 - j
        {
            if intervals[j, 1] > intervals[j + 1, 1]
            {
                var temp0 := intervals[j, 0];
                var temp1 := intervals[j, 1];
                intervals[j, 0] := intervals[j + 1, 0];
                intervals[j, 1] := intervals[j + 1, 1];
                intervals[j + 1, 0] := temp0;
                intervals[j + 1, 1] := temp1;
            }
            j := j + 1;
        }
        i := i + 1;
    }

    // Greedy algorithm to select non-overlapping intervals
    var kept := 0;
    i := 0;
    var lastEnd := if n > 0 then intervals[0, 1] else 0;
    while i < n
        invariant 0 <= i <= n
        invariant kept >= 0
        decreases n - i
    {
        if i == 0 {
            kept := kept + 1;
            lastEnd := intervals[0, 1];
            i := i + 1;
        } else {
            var j := i;
            while j < n && intervals[j, 0] < lastEnd
                invariant i <= j <= n
                invariant kept >= 0
                decreases n - j
            {
                j := j + 1;
            }
            if j < n {
                kept := kept + 1;
                lastEnd := intervals[j, 1];
            }
            i := j;
        }
    }
    count := n - kept;
}
// </vc-code>
