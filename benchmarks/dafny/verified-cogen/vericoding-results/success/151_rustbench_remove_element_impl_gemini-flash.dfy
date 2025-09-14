// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed the helper function as it was syntactically incorrect and not needed for the main task. */
// </vc-helpers>

// <vc-spec>
method RemoveElement(a: array<int>, pos: int) returns (result: seq<int>)
    requires 0 <= pos < a.Length
    ensures |result| == a.Length - 1
    ensures forall i :: 0 <= i < pos ==> result[i] == a[i]
    ensures forall i :: pos <= i < |result| ==> result[i] == a[i + 1]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Implemented the RemoveElement method by constructing the result sequence using array slicing. */
{
  var newSeq := a[0..pos] + a[pos+1..a.Length];
  result := newSeq;
}
// </vc-code>
