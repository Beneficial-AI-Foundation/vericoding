//ATOM


// Bubble Sort
method bubble_sort(a: array2<int>)
  modifies a
  requires a.Length1 == 2
  ensures sorted(a, 0, a.Length0 - 1)
{
  assume sorted(a, 0, a.Length0 - 1);
}


//ATOM


// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
  reads a
  requires a.Length1 == 2
{
  forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}


//IMPL 
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
  
  // Sort intervals by end point using bubble sort
  bubble_sort(intervals);
  
  // Greedy algorithm: select non-overlapping intervals
  var selected := 1; // First interval is always selected
  var lastEnd := intervals[0, 1];
  var i := 1;
  
  /* code modified by LLM (iteration 1): Simplified loop invariants to focus on essential properties that can be verified */
  while i < intervals.Length0
    invariant 1 <= i <= intervals.Length0
    invariant 1 <= selected <= intervals.Length0
    invariant selected <= i
  {
    // If current interval doesn't overlap with the last selected one
    if intervals[i, 0] >= lastEnd {
      selected := selected + 1;
      lastEnd := intervals[i, 1];
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Simplified final calculation with basic bounds check */
  count := intervals.Length0 - selected;
}