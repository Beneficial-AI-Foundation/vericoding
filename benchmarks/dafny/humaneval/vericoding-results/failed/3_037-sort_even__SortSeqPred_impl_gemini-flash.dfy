// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `count` function and removed `indexOf` */
function count(start: int, end_exclusive: int, p: seq<bool>, value: bool): int
  requires 0 <= start <= end_exclusive <= |p|
  ensures 0 <= count(start, end_exclusive, p, value) <= end_exclusive - start
{
  var c := 0;
  for i := start to end_exclusive - 1 {
    if p[i] == value {
      c := c + 1;
    }
  }
  return c;
}

// </vc-helpers>

// <vc-spec>
method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)

  requires |s| == |p|

  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Refactor `SortSeqPred` implementation to correctly handle temporary storage and sorting. */
{
  var tempSorted: array<int> := new int[|s|];
  var pivotedElements: seq<int> := [];

  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant |pivotedElements| == count(0, i, p, true)
    invariant forall k :: 0 <= k < i && !p[k] ==> tempSorted[k] == s[k]
  {
    if p[i] {
      pivotedElements := pivotedElements + [s[i]];
    } else {
      tempSorted[i] := s[i];
    }
  }

  // Sort the pivoted elements
  var pivotArray := new int[|pivotedElements|];
  for i := 0 to |pivotedElements| - 1 {
    pivotArray[i] := pivotedElements[i];
  }

  // This is a placeholder for a sort algorithm. In a real scenario, this would be a full implementation.
  // For this problem, we're assuming a sort function exists that correctly sorts. If this were a real
  // environment, `Array.Sort` or another custom sort would be used and its postconditions proven.
  if |pivotArray| > 1 {
    // Trivial merge sort. In production, this would be e.g. Array.sort
    // {:options "/noNLarith"}
    method MergeSort(arr: array<int>, lo: int, hi: int)
      requires 0 <= lo <= hi <= arr.Length
      modifies arr
      ensures forall i, j :: lo <= i < j < hi ==> arr[i] <= arr[j]
    {
      if hi - lo <= 1 { return; }
      var mid := (lo + hi) / 2;
      MergeSort(arr, lo, mid);
      MergeSort(arr, mid, hi);
      var temp := new int[hi - lo];
      var i := lo;
      var j := mid;
      var k := 0;
      while i < mid && j < hi
        invariant lo <= i <= mid
        invariant mid <= j <= hi
        invariant 0 <= k < hi - lo
      {
        if arr[i] <= arr[j] {
          temp[k] := arr[i];
          i := i + 1;
        } else {
          temp[k] := arr[j];
          j := j + 1;
        }
        k := k + 1;
      }
      while i < mid
        invariant lo <= i <= mid
        invariant 0 <= k < hi - lo
      {
        temp[k] := arr[i];
        i := i + 1;
        k := k + 1;
      }
      while j < hi
        invariant mid <= j <= hi
        invariant 0 <= k < hi - lo
      {
        temp[k] := arr[j];
        j := j + 1;
        k := k + 1;
      }
      for l := 0 to hi - lo - 1 {
        arr[lo + l] := temp[l];
      }
    }
    MergeSort(pivotArray, 0, |pivotArray|);
  }

  var newPivotedElements: seq<int> := [];
  for i := 0 to |pivotArray| - 1 {
      newPivotedElements := newPivotedElements + [pivotArray[i]];
  }

  var pivotedIndex := 0;
  for i := 0 to |s| - 1
    invariant 0 <= i <= |s|
    invariant 0 <= pivotedIndex <= |newPivotedElements|
    invariant forall k :: 0 <= k < i && !p[k] ==> tempSorted[k] == s[k]
    invariant forall k :: 0 <= k < i && p[k] ==> tempSorted[k] == newPivotedElements[count(0, k, p, true) - 1]
    invariant pivotedIndex == count(0, i, p, true)
  {
    if p[i] {
      tempSorted[i] := newPivotedElements[pivotedIndex];
      pivotedIndex := pivotedIndex + 1;
    }
  }

  sorted := tempSorted[..];
}
// </vc-code>
