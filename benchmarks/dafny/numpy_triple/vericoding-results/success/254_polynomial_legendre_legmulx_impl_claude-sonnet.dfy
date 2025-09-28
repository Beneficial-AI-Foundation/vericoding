// <vc-preamble>
// Method to multiply a Legendre series by x
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LegendreMultiplyByX(c: seq<real>) returns (result: seq<real>)
  requires |c| > 0
  ensures |result| == |c| + 1
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed array vs sequence type mismatch - use sequence initialization and update operations */
  result := seq(|c| + 1, _ => 0.0);
  var i := 0;
  while i < |c|
    invariant 0 <= i <= |c|
    invariant |result| == |c| + 1
  {
    if i == 0 {
      result := result[1 := c[0]];
    } else {
      var coeff := c[i];
      var new_val_high := result[i + 1] + coeff * (2.0 * (i as real) + 1.0) / ((i as real) + 1.0);
      var new_val_low := result[i - 1] + coeff * (i as real) / ((i as real) + 1.0);
      result := result[i + 1 := new_val_high][i - 1 := new_val_low];
    }
    i := i + 1;
  }
}
// </vc-code>
