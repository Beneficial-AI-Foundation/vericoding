// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define two's complement function */
function twos(a: int): int {
  -(a + 1)
}

/* helper modified by LLM (iteration 5): prove identities of two's complement for 0 and -1 */
lemma TwosIdentities()
  ensures twos(0) == -1
  ensures twos(-1) == 0
{
  assert twos(0) == -(0 + 1);
  assert -(0 + 1) == -1;
  assert twos(-1) == -((-1) + 1);
  assert -((-1) + 1) == -(0);
  assert -(0) == 0;
}

/* helper modified by LLM (iteration 5): basic sign relations for two's complement */
lemma TwosSignBasic(a: int)
  ensures a > 0 ==> twos(a) < 0
  ensures a <= -1 ==> twos(a) >= 0
{
  if a > 0 {
    assert a + 1 > 0;
    assert -(a + 1) < 0;
  }
  if a <= -1 {
    assert a + 1 <= 0;
    assert -(a + 1) >= 0;
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
  /* code modified by LLM (iteration 5): build result via sequence comprehension using two's complement */
  result := seq(i | 0 <= i < |x| :: twos(x[i]));
}
// </vc-code>
