// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The function signature had `returns` which is not allowed. Changed to a function expression. Renamed to avoid using `Negate` for consistency. */
function InvertValue(value: int): int { -(value + 1) }
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
/* code modified by LLM (iteration 5): The previous code used `Negate` function, which had a compilation error. Changed to `InvertValue` instead, and simplified the loop to use `result` directly.*/
{
  var temp_result := new int[|x|];
  for i := 0 to |x| - 1 {
    temp_result[i] := InvertValue(x[i]);
  }
  result := temp_result;
}
// </vc-code>
