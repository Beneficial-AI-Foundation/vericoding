// <vc-helpers>
// Helper predicate to check if a sequence is ordered up to a certain index
predicate IsOrderedUpTo(arr: seq<int>, idx: int)
{
  idx <= |arr| && forall i :: 0 <= i < idx - 1 ==> arr[i] <= arr[i+1]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method can_arrange(arr: seq<int>) returns (pos: int)
Create a function which returns the largest index of an element which is not greater than or equal to the element immediately preceding it. If no such element exists then return -1.
*/
// </vc-description>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (pos: int)
  requires |arr| > 0
  ensures pos == -1 ==> forall i :: 0 <= i < |arr| - 1 ==> arr[i] <= arr[i+1]
  ensures pos >= 0 ==> 0 <= pos < |arr| && arr[pos-1] > arr[pos]
  ensures pos >= 0 ==> forall i :: 0 <= i < pos - 1 ==> arr[i] <= arr[i+1]
// </vc-spec>
// <vc-code>
{
  if |arr| == 1 {
    return -1;
  }
  
  var i := 1;
  while i < |arr|
    invariant 1 <= i <= |arr|
    invariant forall k :: 0 <= k < i - 1 ==> arr[k] <= arr[k+1]
  {
    if arr[i-1] > arr[i] {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
// </vc-code>
