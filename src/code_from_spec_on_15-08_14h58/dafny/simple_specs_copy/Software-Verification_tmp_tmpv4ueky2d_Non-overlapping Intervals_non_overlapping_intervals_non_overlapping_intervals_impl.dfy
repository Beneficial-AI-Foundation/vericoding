method bubble_sort(a: array2<int>)
  modifies a
  requires a.Length1 == 2
  ensures sorted(a, 0, a.Length0 - 1)
{
  /* code modified by LLM (iteration 1): implemented bubble sort instead of using assume */
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
  {
    var j := 0;
    while j < a.Length0 - i - 1
      invariant 0 <= j <= a.Length0 - i - 1
    {
      if a[j, 1] > a[j + 1, 1] {
        // Swap elements
        var temp0 := a[j, 0];
        var temp1 := a[j, 1];
        a[j, 0] := a[j + 1, 0];
        a[j, 1] := a[j + 1, 1];
        a[j + 1, 0] := temp0;
        a[j + 1, 1] := temp1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
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
  ensures count >= 0
{
  if intervals.Length0 <= 1 {
    /* code modified by LLM (iteration 1): fixed return value for edge case */
    count := 0;
    return;
  }
  
  // Sort intervals by end time using bubble sort
  bubble_sort(intervals);
  
  var kept := 1; // Number of intervals we keep;
  var lastEnd := intervals[0, 1]; // End time of last kept interval;
  
  var i := 1;
  while i < intervals.Length0
    invariant 1 <= i <= intervals.Length0
    invariant kept >= 1
    /* code modified by LLM (iteration 1): added upper bound invariant for kept */
    invariant kept <= i
  {
    // If current interval doesn't overlap with last kept interval
    if intervals[i, 0] >= lastEnd {
      kept := kept + 1;
      lastEnd := intervals[i, 1];
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): ensure count is non-negative */
  count := intervals.Length0 - kept;
}