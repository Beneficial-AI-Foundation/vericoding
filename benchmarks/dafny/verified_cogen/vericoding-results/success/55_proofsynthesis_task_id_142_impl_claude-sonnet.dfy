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
/* helper modified by LLM (iteration 3): fixed lemma to handle empty sequence case correctly */
lemma CountIdenticalExtend(s1: seq<int>, s2: seq<int>, s3: seq<int>, x1: int, x2: int, x3: int)
    requires |s1| == |s2| == |s3|
    ensures CountIdentical(s1 + [x1], s2 + [x2], s3 + [x3]) == 
            CountIdentical(s1, s2, s3) + (if x1 == x2 && x2 == x3 then 1 else 0)
{
    if |s1| == 0 {
        assert s1 == [];
        assert s2 == [];
        assert s3 == [];
        assert CountIdentical(s1, s2, s3) == 0;
    } else {
        var ext1 := s1 + [x1];
        var ext2 := s2 + [x2];
        var ext3 := s3 + [x3];
        assert ext1[..|ext1|-1] == s1;
        assert ext2[..|ext2|-1] == s2;
        assert ext3[..|ext3|-1] == s3;
        assert ext1[|ext1|-1] == x1;
        assert ext2[|ext2|-1] == x2;
        assert ext3[|ext3|-1] == x3;
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
{
    /* code modified by LLM (iteration 3): fixed loop invariant and lemma application */
    count := 0;
    var i := 0;
    while i < arr1.Length
        invariant 0 <= i <= arr1.Length
        invariant count == CountIdentical(arr1[..i], arr2[..i], arr3[..i])
        invariant 0 <= count <= i
    {
        assert arr1[..i+1] == arr1[..i] + [arr1[i]];
        assert arr2[..i+1] == arr2[..i] + [arr2[i]];
        assert arr3[..i+1] == arr3[..i] + [arr3[i]];
        
        CountIdenticalExtend(arr1[..i], arr2[..i], arr3[..i], arr1[i], arr2[i], arr3[i]);
        
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count := count + 1;
        }
        i := i + 1;
    }
    assert i == arr1.Length;
    assert arr1[..i] == arr1[..];
    assert arr2[..i] == arr2[..];
    assert arr3[..i] == arr3[..];
}
// </vc-code>
