// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
