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
/* helper modified by LLM (iteration 2): Added lemma to prove loop invariant maintenance */
lemma CountIdenticalAppend(s1: seq<int>, s2: seq<int>, s3: seq<int>, v1: int, v2: int, v3: int)
    requires |s1| == |s2| == |s3|
    ensures CountIdentical(s1 + [v1], s2 + [v2], s3 + [v3]) == CountIdentical(s1, s2, s3) + if v1 == v2 && v2 == v3 then 1 else 0
{
    if |s1| == 0 {
        assert s1 + [v1] == [v1];
        assert s2 + [v2] == [v2];
        assert s3 + [v3] == [v3];
    } else {
        assert (s1 + [v1])[..|s1 + [v1]| - 1] == s1;
        assert (s2 + [v2])[..|s2 + [v2]| - 1] == s2;
        assert (s3 + [v3])[..|s3 + [v3]| - 1] == s3;
        assert (s1 + [v1])[|s1 + [v1]| - 1] == v1;
        assert (s2 + [v2])[|s2 + [v2]| - 1] == v2;
        assert (s3 + [v3])[|s3 + [v3]| - 1] == v3;
    }
}
// </vc-helpers>

// <vc-spec>
method CountIdenticalPosition(arr1: array<int>, arr2: array<int>, arr3: array<int>) returns (count: nat)
    requires arr1.Length == arr2.Length && arr2.Length == arr3.Length
    ensures 0 <= count <= arr1.Length
    ensures CountIdentical(arr1[..], arr2[..], arr3[..]) == count
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed loop invariant and added proper counting logic */
{
    count := 0;
    var i := 0;
    while i < arr1.Length
        invariant 0 <= i <= arr1.Length
        invariant 0 <= count <= i
        invariant count == CountIdentical(arr1[..i], arr2[..i], arr3[..i])
    {
        assert arr1[..i+1] == arr1[..i] + [arr1[i]];
        assert arr2[..i+1] == arr2[..i] + [arr2[i]];
        assert arr3[..i+1] == arr3[..i] + [arr3[i]];
        CountIdenticalAppend(arr1[..i], arr2[..i], arr3[..i], arr1[i], arr2[i], arr3[i]);
        
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count := count + 1;
        }
        i := i + 1;
    }
    assert i == arr1.Length;
    assert arr1[..] == arr1[..arr1.Length];
    assert arr2[..] == arr2[..arr2.Length];
    assert arr3[..] == arr3[..arr3.Length];
}
// </vc-code>
