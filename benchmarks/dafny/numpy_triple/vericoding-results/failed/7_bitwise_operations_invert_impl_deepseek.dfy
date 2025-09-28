// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function invert_element(n: int): int
  ensures invert_element(n) == -(n + 1)
{
  -(n + 1)
}

lemma invert_element_properties(n: int)
  ensures invert_element(n) == -(n + 1)
  ensures n == 0 ==> invert_element(n) == -1
  ensures n == -1 ==> invert_element(n) == 0
  ensures n != -1 ==> (n > 0 <==> invert_element(n) < 0)
{
  /* helper modified by LLM (iteration 5): Added lemma to prove key properties of invert_element */
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
  /* code modified by LLM (iteration 5): Simplified implementation using invert_element lemma */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == invert_element(x[j])
  {
    var inverted := invert_element(x[i]);
    invert_element_properties(x[i]); // Prove properties for this specific value
    result := result + [inverted];
    i := i + 1;
  }
}
// </vc-code>
