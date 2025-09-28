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
function IsOdd(x: int): bool { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
method FindFirstOdd(arr: array<int>) returns (index: int)
    ensures CheckFindFirstOdd(arr[..], index)
// </vc-spec>
// <vc-code>
{
  index := -1;
  var i := 0;
  while index == -1 && i < arr.Length
    invariant -1 <= index < arr.Length
    invariant 0 <= i <= arr.Length
    invariant (index == -1) ==> (forall k :: 0 <= k < i ==> arr[k] % 2 == 0)
    invariant (index != -1) ==> (0 <= index < arr.Length && arr[index] % 2 != 0 && (forall k :: 0 <= k < index ==> arr[k] % 2 == 0))
  {
    if arr[i] % 2 != 0 {
      index := i;
    } else {
      i := i + 1;
    }
  }
}
// </vc-code>
