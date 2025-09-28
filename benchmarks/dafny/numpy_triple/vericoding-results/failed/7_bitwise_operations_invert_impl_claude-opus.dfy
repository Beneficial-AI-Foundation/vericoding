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
  /* code modified by LLM (iteration 2): Added assertions to help verify sign flipping property */
  result := [];
  for i := 0 to |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == -(x[j] + 1)
    invariant forall j :: 0 <= j < i ==> x[j] == 0 ==> result[j] == -1
    invariant forall j :: 0 <= j < i ==> x[j] == -1 ==> result[j] == 0
    invariant forall j :: 0 <= j < i ==> x[j] != -1 ==> (x[j] > 0 <==> result[j] < 0)
  {
    var newElement := -(x[i] + 1);
    assert x[i] == 0 ==> newElement == -1;
    assert x[i] == -1 ==> newElement == 0;
    assert x[i] != -1 ==> (x[i] > 0 <==> newElement < 0) by {
      if x[i] != -1 {
        if x[i] > 0 {
          assert x[i] >= 1;
          assert x[i] + 1 >= 2;
          assert -(x[i] + 1) <= -2;
          assert newElement < 0;
        } else {
          assert x[i] < -1;
          assert x[i] + 1 < 0;
          assert -(x[i] + 1) > 0;
          assert newElement > 0;
        }
      }
    }
    result := result + [newElement];
  }
}
// </vc-code>
