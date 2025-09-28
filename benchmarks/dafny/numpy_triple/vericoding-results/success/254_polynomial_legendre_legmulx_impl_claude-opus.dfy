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
  /* code modified by LLM (iteration 2): Fixed type casting syntax from real() to 'as real' */
  result := [0.0] + c;
  var i := 0;
  var temp := [];
  while i < |c|
    invariant 0 <= i <= |c|
    invariant |temp| == i
  {
    if i == 0 {
      temp := temp + [c[0] / 3.0];
    } else {
      var val := (i as real * c[i-1] + (i+1) as real * c[i]) / (2.0 * i as real + 1.0);
      temp := temp + [val];
    }
    i := i + 1;
  }
  temp := temp + [|c| as real * c[|c|-1] / (2.0 * |c| as real + 1.0)];
  result := temp;
}
// </vc-code>
