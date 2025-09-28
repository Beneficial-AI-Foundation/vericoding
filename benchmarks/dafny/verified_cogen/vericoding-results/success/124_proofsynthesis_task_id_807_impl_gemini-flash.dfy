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
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant (forall k :: 0 <= k < i ==> arr[k] % 2 == 0)
    {
        if arr[i] % 2 != 0 {
            return i;
        }
        i := i + 1;
    }
    return -1;
}
// </vc-code>
