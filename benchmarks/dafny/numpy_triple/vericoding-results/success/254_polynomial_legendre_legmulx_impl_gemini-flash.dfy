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
/* code modified by LLM (iteration 4): Fixed compilation error by directly assigning to result as a sequence, creating an array and then converting to sequence to ensure type compatibility. */
{
  var n := |c|;
  var result_arr := new real[n + 1];
  result := result_arr[..];

  if n == 1 {
    result_arr[0] := 0.0;
    result_arr[1] := c[0];
  } else {
    result_arr[0] := 0.0;
    result_arr[1] := c[0];
    for i := 1 to n - 1
      invariant 1 <= i <= n
      invariant result_arr.Length == n + 1
    {
      result_arr[i+1] := c[i];
    }
  }
}
// </vc-code>
