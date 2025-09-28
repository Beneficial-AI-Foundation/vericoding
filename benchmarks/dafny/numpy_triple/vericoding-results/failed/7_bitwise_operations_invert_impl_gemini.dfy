// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added lemmas to help prove identity properties. */
lemma InvertForZero(x: int, res: int)
  requires res == -(x + 1)
  ensures x == 0 ==> res == -1
{}

lemma InvertForNegOne(x: int, res: int)
  requires res == -(x + 1)
  ensures x == -1 ==> res == 0
{}
// </vc-helpers>

// <vc-spec>
method invert(x: seq<int>) returns (result: seq<int>)
  // The result has the same length as the input
  ensures |result| == |x|
  // Each element follows the two's complement relationship: ~x = -(x + 1)  
  ensures forall i :: 0 <= i < |x| ==> result[i] == -(x[i] + 1)
  // Identity property for zero
  ensures forall i :: 0 <= i < |x| ==> x[i] == 0 ==> result[i] == -1
  // Identity property for negative one
  ensures forall i :: 0 <= i < |x| ==> x[i] == -1 ==> result[i] == 0
  // Sign flipping property
  ensures forall i :: 0 <= i < |x| ==> x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0)
  // Identity properties follow from the main relationship:
  // When x[i] == 0: result[i] == -(0 + 1) == -1
  // When x[i] == -1: result[i] == -(-1 + 1) == 0
  // Sign flipping: when x[i] != -1, x[i] > 0 <==> result[i] < 0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added invariant and decreases clause to aid verification. */
  var i := 0;
  result := [];
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == -(x[j] + 1)
    decreases |x| - i
  {
    result := result + [-(x[i] + 1)];
    i := i + 1;
  }
}
// </vc-code>
