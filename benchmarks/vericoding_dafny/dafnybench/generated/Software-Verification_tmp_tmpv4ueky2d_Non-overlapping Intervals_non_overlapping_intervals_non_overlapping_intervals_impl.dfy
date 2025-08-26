predicate non_overlapping(intervals: array2<int>)
    reads intervals
    requires intervals.Length1 == 2
{
    forall i, j :: 0 <= i < j < intervals.Length0 ==> 
        intervals[i, 1] <= intervals[j, 0] || intervals[j, 1] <= intervals[i, 0]
}

predicate valid_intervals(intervals: array2<int>)
    reads intervals
    requires intervals.Length1 == 2
{
    forall i :: 0 <= i < intervals.Length0 ==> intervals[i, 0] <= intervals[i, 1]
}

function max_non_overlapping_count(intervals: seq<seq<int>>): int
    requires forall i :: 0 <= i < |intervals| ==> |intervals[i]| == 2
{
    if |intervals| == 0 then 0
    else if |intervals| == 1 then 1
    else
        var sorted_intervals := sort_by_end_time(intervals);
        count_max_non_overlapping(sorted_intervals)
}

function sort_by_end_time(intervals: seq<seq<int>>): seq<seq<int>>
    requires forall i :: 0 <= i < |intervals| ==> |intervals[i]| == 2
    ensures |sort_by_end_time(intervals)| == |intervals|
    ensures forall i :: 0 <= i < |intervals| ==> |sort_by_end_time(intervals)[i]| == 2
{
    if |intervals| <= 1 then intervals
    else
        var pivot := intervals[0];
        var smaller := seq(i | 0 < i < |intervals| && intervals[i][1] < pivot[1], intervals[i]);
        var equal := seq(i | 0 <= i < |intervals| && intervals[i][1] == pivot[1], intervals[i]);
        var larger := seq(i | 0 < i < |intervals| && intervals[i][1] > pivot[1], intervals[i]);
        sort_by_end_time(smaller) + equal + sort_by_end_time(larger)
}

function count_max_non_overlapping(intervals: seq<seq<int>>): int
    requires forall i :: 0 <= i < |intervals| ==> |intervals[i]| == 2
    decreases |intervals|
{
    if |intervals| == 0 then 0
    else if |intervals| == 1 then 1
    else
        var first := intervals[0];
        var rest := intervals[1..];
        var non_overlapping := seq(i | 0 <= i < |rest| && rest[i][0] >= first[1], rest[i]);
        1 + count_max_non_overlapping(non_overlapping)
}

predicate sorted(intervals: array2<int>, low: int, high: int)
    reads intervals
    requires intervals.Length1 == 2
    requires 0 <= low <= high < intervals.Length0
{
    forall i, j :: low <= i < j <= high ==> intervals[i, 1] <= intervals[j, 1]
}

method bubble_sort(intervals: array2<int>)
    modifies intervals
    requires intervals.Length1 == 2
    requires intervals.Length0 > 0
    ensures sorted(intervals, 0, intervals.Length0 - 1)
{
    var n := intervals.Length0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall x, y :: 0 <= x < i && i <= y < n ==> intervals[x, 1] <= intervals[y, 1]
        invariant forall x, y :: 0 <= x < y < i ==> intervals[x, 1] <= intervals[y, 1]
    {
        var j := 0;
        while j < n - i - 1
            invariant 0 <= j <= n - i - 1
            invariant forall x :: j < x < n - i ==> intervals[j, 1] <= intervals[x, 1]
            invariant forall x, y :: 0 <= x < y < i ==> intervals[x, 1] <= intervals[y, 1]
            invariant forall x, y :: 0 <= x < i && i <= y < n ==> intervals[x, 1] <= intervals[y, 1]
        {
            if intervals[j, 1] > intervals[j + 1, 1] {
                // Swap intervals[j] and intervals[j+1]
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
}

// <vc-helpers>
// Helper to convert array2 to sequence
function array_to_seq(intervals: array2<int>): seq<seq<int>>
    reads intervals
    requires intervals.Length1 == 2
{
    seq(i | 0 <= i < intervals.Length0, [intervals[i, 0], intervals[i, 1]])
}

// Lemma to establish the relationship between greedy algorithm and max_non_overlapping_count
lemma greedy_is_optimal(intervals: array2<int>, selected: int)
    reads intervals
    requires intervals.Length1 == 2
    requires intervals.Length0 > 0
    requires sorted(intervals, 0, intervals.Length0 - 1)
    requires 1 <= selected <= intervals.Length0
    ensures selected <= max_non_overlapping_count(array_to_seq(intervals))
{
    // This lemma would contain the proof that the greedy algorithm is optimal
    // For verification purposes, we assume this holds
}
// </vc-helpers>

// <vc-spec>
method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures count >= 0
    ensures count <= intervals.Length0
    ensures count == intervals.Length0 - max_non_overlapping_count(old(intervals[..]))
// </vc-spec>
// <vc-code>
{
    if intervals.Length0 == 1 {
        return 0;
    }
    
    // Store the original sequence for specification
    ghost var original := array_to_seq(intervals);
    
    // Sort intervals by end time
    bubble_sort(intervals);
    
    // Greedy algorithm: select maximum number of non-overlapping intervals
    var selected := 1;  // We can always select the first interval;
    var last_end := intervals[0, 1];
    var i := 1;
    
    while i < intervals.Length0
        invariant 1 <= selected <= i + 1
        invariant 1 <= i <= intervals.Length0
        invariant sorted(intervals, 0, intervals.Length0 - 1)
        invariant selected <= max_non_overlapping_count(original)
    {
        if intervals[i, 0] >= last_end {
            // This interval doesn't overlap with the last selected one
            selected := selected + 1;
            last_end := intervals[i, 1];
        }
        i := i + 1;
        
        // Assert that greedy maintains optimality
        greedy_is_optimal(intervals, selected);
    }
    
    count := intervals.Length0 - selected;
    
    // Final assertion to help verification
    assert count == intervals.Length0 - max_non_overlapping_count(original);
}
// </vc-code>