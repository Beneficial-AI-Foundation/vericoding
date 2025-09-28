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
  var n := |c|;
  var d := new real[n + 1];

  d[1] := c[0];

  var i := 1;
  while i < n
    invariant 1 <= i <= n
  {
    var i_real := i as real;
    var den := 2.0 * i_real + 1.0;
    d[i-1] := d[i-1] + c[i] * (i_real / den);
    d[i+1] := d[i+1] + c[i] * ((i_real + 1.0) / den);
    i := i + 1;
  }

  result := d[..];
}
// </vc-code>
