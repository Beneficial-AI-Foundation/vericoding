// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ComputeResult(arr: seq<int>, index: nat): seq<int>
    requires index < |arr|
    ensures |ComputeResult(arr, index)| == |arr|
    ensures ComputeResult(arr, index)[index] == 60
    ensures forall k :: 0 <= k < |arr| && k != index ==> ComputeResult(arr, index)[k] == arr[k]
{
    arr[index := 60]
}
// </vc-helpers>

// <vc-spec>
method TestArrayElements(a: seq<int>, j: nat) returns (result: seq<int>)
    requires j < |a|
    ensures |result| == |a|
    ensures result[j] == 60
    ensures forall k :: 0 <= k < |a| && k != j ==> result[k] == a[k]
// </vc-spec>
// <vc-code>
{
  result := ComputeResult(a, j);
}
// </vc-code>
