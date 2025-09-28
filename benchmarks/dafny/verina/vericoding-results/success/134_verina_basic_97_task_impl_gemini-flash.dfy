// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed 'method' keyword to fix compilation error. */
function UpdateSeq(s: seq<int>, index: nat, value: int): seq<int>
    requires index < |s|
    ensures |UpdateSeq(s, index, value)| == |s|
    ensures UpdateSeq(s, index, value)[index] == value
    ensures forall k | 0 <= k < |s| && k != index :: UpdateSeq(s, index, value)[k] == s[k]
{
    s[index := value]
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
/* code modified by LLM (iteration 2): Implemented the method using the UpdateSeq helper. */
{
    result := UpdateSeq(a, j, 60);
}
// </vc-code>
