// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function AppendElem(a: seq<int>, b: int): seq<int> { a + [b] }
// </vc-helpers>

// <vc-spec>
method ArrayAppend(a: seq<int>, b: int) returns (result: seq<int>)
    ensures |result| == |a| + 1
    ensures forall i :: 0 <= i < |result| ==> result[i] == (if i < |a| then a[i] else b)
// </vc-spec>
// <vc-code>
{
  result := AppendElem(a, b);
}
// </vc-code>
