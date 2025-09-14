// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method FindFirstOccurrence(arr: array<int>, target: int) returns (index: int)

    requires
        forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]

    ensures
        if index >= 0 then (
            && 0 <= index < arr.Length
            && (forall k :: 0 <= k < index ==> arr[k] != target)
            && arr[index] == target
        ) else (
            forall k :: 0 <= k < arr.Length ==> arr[k] != target
        )
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var found := false;
    var idx := -1;
    while i < arr.Length
      invariant 0 <= i <= arr.Length
      invariant (!found) ==> (forall k :: 0 <= k < i ==> arr[k] != target)
      invariant found ==> 0 <= idx < arr.Length && arr[idx] == target && forall k :: 0 <= k < idx ==> arr[k] != target
    {
      if (!found) {
        if arr[i] == target {
          found := true;
          idx := i;
        }
      }
      i := i + 1;
    }
    if found {
      index := idx;
    } else {
      index := -1;
    }
}
// </vc-code>
