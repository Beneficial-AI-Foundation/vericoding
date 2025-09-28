// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

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
  /* code modified by LLM (iteration 2): implemented sequence slicing */
  var fullSeq := a[..];
  result := fullSeq[0..pos] + fullSeq[pos+1..];
}
// </vc-code>
