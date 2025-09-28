// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ArrayToSeq(a: array<int>): seq<int>
    reads a
{
    a[..]
}

function RemoveAtIndex(s: seq<int>, pos: int): seq<int>
    requires 0 <= pos < |s|
    ensures |RemoveAtIndex(s, pos)| == |s| - 1
    ensures forall i :: 0 <= i < pos ==> RemoveAtIndex(s, pos)[i] == s[i]
    ensures forall i :: pos <= i < |RemoveAtIndex(s, pos)| ==> RemoveAtIndex(s, pos)[i] == s[i + 1]
{
    s[..pos] + s[pos + 1..]
}
// </vc-helpers>

// <vc-spec>
method RemoveElement(a: array<int>, pos: int) returns (result: seq<int>)
    requires 0 <= pos < a.Length
    ensures |result| == a.Length - 1
    ensures forall i :: 0 <= i < pos ==> result[i] == a[i]
    ensures forall i :: pos <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
{
    var arraySeq := ArrayToSeq(a);
    result := RemoveAtIndex(arraySeq, pos);
}
// </vc-code>
