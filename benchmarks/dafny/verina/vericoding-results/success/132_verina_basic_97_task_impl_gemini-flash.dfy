// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function CreateNewSeq(a: seq<int>, j: nat, value: int): seq<int>
{
    if 0 <= j < |a| then
        a[0..j] + [value] + a[j+1..]
    else
        a
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
    result := CreateNewSeq(a, j, 60);
}
// </vc-code>
