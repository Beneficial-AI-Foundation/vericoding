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


//IMPL non_overlapping_intervals
method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
  modifies intervals
  requires 1 <= intervals.Length0 <= 100000
  requires intervals.Length1 == 2
  requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
  requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
  ensures count >= 0
{
  if intervals.Length0 <= 1 {
    count := 0;
    return;
  }
  
  // Sort intervals by end point using the provided bubble_sort
  bubble_sort(intervals);
  
  var non_overlapping := 1; // Count of non-overlapping intervals we keep
  var last_end := intervals[0, 1];
  var i := 1;
  
  while i < intervals.Length0
    invariant 1 <= i <= intervals.Length0
    invariant non_overlapping >= 1
    invariant non_overlapping <= i
  {
    // If current interval doesn't overlap with the last selected interval
    if intervals[i, 0] >= last_end {
      non_overlapping := non_overlapping + 1;
      last_end := intervals[i, 1];
    }
    i := i + 1;
  }
  
  count := intervals.Length0 - non_overlapping;
}