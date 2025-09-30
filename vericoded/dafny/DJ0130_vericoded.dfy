// <vc-preamble>
predicate CheckFindFirstOdd(arr: seq<int>, index: int)
{
    if index >= 0 then
        && 0 <= index < |arr|
        && (forall k :: 0 <= k < index ==> arr[k] % 2 == 0)
        && arr[index] % 2 != 0
    else
        forall k :: 0 <= k < |arr| ==> arr[k] % 2 == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindFirstOdd(arr: array<int>) returns (index: int)
    ensures CheckFindFirstOdd(arr[..], index)
// </vc-spec>
// <vc-code>
{
  index := 0;
  while index < arr.Length
    invariant 0 <= index <= arr.Length
    invariant forall k :: 0 <= k < index ==> arr[k] % 2 == 0
  {
    if arr[index] % 2 != 0 {
      return;
    }
    index := index + 1;
  }
  index := -1;
}
// </vc-code>
