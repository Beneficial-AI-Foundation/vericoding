// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method swap(arr: seq<int>, i: int, j: int) returns (result: seq<int>)
    requires 0 <= i < |arr|
    requires 0 <= j < |arr|
    ensures |result| == |arr|
    ensures result[i] == arr[j]
    ensures result[j] == arr[i]
    ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> result[k] == arr[k]
// </vc-spec>
// <vc-code>
{
  var newSeq := arr;
  newSeq := newSeq[i := arr[j]][j := arr[i]];
  result := newSeq;
}
// </vc-code>
