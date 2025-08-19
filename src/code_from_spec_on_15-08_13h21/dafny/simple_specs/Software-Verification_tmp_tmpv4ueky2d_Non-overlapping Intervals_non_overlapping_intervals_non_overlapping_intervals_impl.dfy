//ATOM


// Bubble Sort
method bubble_sort(a: array2<int>)
  modifies a
  requires a.Length1 == 2
  ensures sorted(a, 0, a.Length0 - 1)
{
  assume {:axiom} sorted(a, 0, a.Length0 - 1);
}


//ATOM


// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
  reads a
  requires a.Length1 == 2
{
  forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}


// IMPL non_overlapping_intervals
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
  
  // Sort intervals by end point using the provided bubble_sort
  bubble_sort(intervals);
  
  /* code modified by LLM (iteration 1): Fixed loop invariants and variable tracking */
  // Greedy algorithm: keep track of non-overlapping intervals
  var keep := 1; // We can always keep at least the first interval;
  var lastEnd := intervals[0, 1];
  var lastKeptIndex := 0; // Track the index of the last kept interval;
  var i := 1;
  
  while i < intervals.Length0
    invariant 1 <= i <= intervals.Length0
    invariant keep >= 1
    invariant keep <= i
    invariant sorted(intervals, 0, intervals.Length0 - 1)
    invariant 0 <= lastKeptIndex < i
    invariant lastEnd == intervals[lastKeptIndex, 1]
  {
    // If current interval doesn't overlap with the last kept interval
    if intervals[i, 0] >= lastEnd {
      keep := keep + 1;
      /* code modified by LLM (iteration 1): Update both lastEnd and lastKeptIndex to maintain invariant */
      lastEnd := intervals[i, 1];
      lastKeptIndex := i;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Ensured count calculation maintains non-negativity */
  count := intervals.Length0 - keep;
}