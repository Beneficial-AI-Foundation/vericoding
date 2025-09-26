// <vc-preamble>
method UpdateInner(a: seq<nat>, idx: int, val: nat) returns (result: seq<nat>)
    requires 0 <= idx < |a|
    ensures |result| == |a|
    ensures result[idx] == val
    ensures forall i :: 0 <= i < |a| && i != idx ==> result[i] == a[i]
{
    result := a[idx := val];
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ModifyArrayElement(arr: seq<seq<nat>>, index1: int, index2: int, val: nat) returns (result: seq<seq<nat>>)
    requires 0 <= index1 < |arr|
    requires 0 <= index2 < |arr[index1]|
    ensures |result| == |arr|
    ensures forall i :: 0 <= i < |arr| && i != index1 ==> result[i] == arr[i]
    ensures |result[index1]| == |arr[index1]|
    ensures forall j :: 0 <= j < |arr[index1]| && j != index2 ==> result[index1][j] == arr[index1][j]
    ensures result[index1][index2] == val
// </vc-spec>
// <vc-code>
{
    // impl-start
    var updatedInner := UpdateInner(arr[index1], index2, val);
    result := arr[index1 := updatedInner];
    // impl-end
}
// </vc-code>
