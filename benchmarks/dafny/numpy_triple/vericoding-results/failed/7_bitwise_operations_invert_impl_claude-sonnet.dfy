// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to prove sign flipping property with corrected case analysis */
lemma SignFlippingProperty(x: int, result: int)
  requires result == -(x + 1)
  requires x != -1
  ensures x > 0 <==> result < 0
{
  if x > 0 {
    assert result == -(x + 1) < -1 < 0;
  } else {
    assert x < 0 && x != -1;
    assert x <= -2;
    assert x + 1 <= -1;
    assert -(x + 1) >= 1 > 0;
  }
}
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
  /* code modified by LLM (iteration 5): simplified implementation without problematic assertions */
  result := seq(|x|, i requires 0 <= i < |x| => -(x[i] + 1));
  
  // Help Dafny prove the sign flipping property
  assert forall i :: 0 <= i < |x| ==> x[i] != -1 ==> (x[i] > 0 <==> result[i] < 0) by {
    forall i | 0 <= i < |x| && x[i] != -1
      ensures x[i] > 0 <==> result[i] < 0
    {
      SignFlippingProperty(x[i], result[i]);
    }
  }
}
// </vc-code>
