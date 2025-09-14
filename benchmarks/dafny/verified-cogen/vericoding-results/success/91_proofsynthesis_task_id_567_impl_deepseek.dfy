// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Simplified helpers with proper reads clauses */
predicate IsSortedSegment(arr: array<int>, start: int, end: int)
  requires 0 <= start <= end <= arr.Length
  reads arr
{
  forall i, j :: start <= i < j < end ==> arr[i] <= arr[j]
}
// </vc-helpers>

// <vc-spec>
method IsSorted(arr: array<int>) returns (is_sorted: bool)

    requires
        arr.Length > 0

    ensures
        is_sorted == (forall i, j :: 0 <= i < j < arr.Length ==> (arr[i] <= arr[j]))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed verification with proper inductive approach */
{
  is_sorted := true;
  
  if arr.Length == 1 {
    return;
  }
  
  var k := 0;
  while k < arr.Length - 1
    invariant 0 <= k <= arr.Length - 1
    invariant is_sorted ==> (forall i :: 0 <= i <= k ==> arr[i] <= arr[k])
    invariant is_sorted ==> IsSortedSegment(arr, 0, k + 1)
  {
    if arr[k] > arr[k + 1] {
      is_sorted := false;
      return;
    }
    k := k + 1;
  }
}
// </vc-code>
