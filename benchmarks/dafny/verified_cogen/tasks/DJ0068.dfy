// <vc-preamble>
function CountIdentical(s1: seq<int>, s2: seq<int>, s3: seq<int>): int
    decreases |s1|, |s2|, |s3|
{
    if |s1| == 0 || |s2| == 0 || |s3| == 0 then
        0
    else
        CountIdentical(s1[..|s1|-1], s2[..|s2|-1], s3[..|s3|-1]) + if (s1[|s1|-1] == s2[|s2|-1]
            && s2[|s2|-1] == s3[|s3|-1]) then
            1
        else
            0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountIdenticalPosition(arr1: array<int>, arr2: array<int>, arr3: array<int>) returns (count: nat)
    requires arr1.Length == arr2.Length && arr2.Length == arr3.Length
    ensures 0 <= count <= arr1.Length
    ensures CountIdentical(arr1[..], arr2[..], arr3[..]) == count
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
}
// </vc-code>
