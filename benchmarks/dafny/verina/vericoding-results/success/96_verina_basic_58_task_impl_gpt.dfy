// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' and implemented recursive doubling of sequence elements */
function DoubleSeq(s: seq<int>): seq<int>
  decreases |s|
  ensures |DoubleSeq(s)| == |s|
  ensures forall i :: 0 <= i < |s| ==> DoubleSeq(s)[i] == 2 * s[i]
{
  if |s| == 0 then []
  else DoubleSeq(s[..|s|-1]) + [2 * s[|s|-1]]
}
// </vc-helpers>

// <vc-spec>
method DoubleArrayElements(s: seq<int>) returns (result: seq<int>)
    ensures |result| == |s|
    ensures forall i :: 0 <= i < |s| ==> result[i] == 2 * s[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute result by calling the helper function */
  result := DoubleSeq(s);
}
// </vc-code>
