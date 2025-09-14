// <vc-preamble>
predicate isSorted(a:array<int>)
  reads a
{
  forall i:nat, j:nat :: i <= j < a.Length ==> a[i] <= a[j]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
// </vc-spec>
// <vc-code>
{
  b := false;
  var low: int := 0;
  var high: int := a.Length;

  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: (0 <= i < low || high <= i < a.Length) ==> a[i] != K
  {
    var mid := low + (high - low) / 2;
    if a[mid] < K {
      low := mid + 1;
    } else if a[mid] > K {
      high := mid;
    } else {
      b := true;
      return;
    }
  }
}
// </vc-code>
