// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma InvertSignFlippingLemma(x: int)
  ensures x == -1 || ((x > 0) <==> (- (x + 1) < 0))
{
  if x == -1 {
  } else if x > 0 {
    assert x + 1 > 0;
    assert (-(x + 1)) < 0;
    assert ((x > 0) <==> ((- (x + 1)) < 0));
  } else {
    assert x <= 0;
    if x == 0 {
      assert x + 1 == 1 > 0;
      assert x > 0 == false;
      assert -(x + 1) == -1 < 0;
      assert ((x > 0) <==> ((- (x + 1)) < 0));
    } else {
      assert x <= -1;
      assert x + 1 <= -1;
      assert x <= -1 ==> -(x + 1) >= 1 > 0;
      assert -(x + 1) < 0 == false;
      assert x > 0 == false;
      assert ((x > 0) <==> ((- (x + 1)) < 0));
    }
  }
  // helper modified by LLM (iteration 5): fixed assertion in else branch, added case for x==0, and added false ensures for negative ints
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
  /* code modified by LLM (iteration 5): added loop invariants, and call to helper lemma for each element to prove ensures */
  result := [];
  var i := 0;
  while i < |x| 
  decreases |x| - i
  invariant 0 <= i <= |x|
  invariant |result| == i
  invariant forall j :: 0 <= j < i ==> result[j] == -(x[j] + 1)
  {
    result := result + [- (x[i] + 1)];
    InvertSignFlippingLemma(x[i]);
    i := i + 1;
  }
}
// </vc-code>
