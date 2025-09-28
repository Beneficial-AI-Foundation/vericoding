// <vc-preamble>
// Method to multiply a Legendre series by x
// </vc-preamble>

// <vc-helpers>
function UpCoeff(k: int): real
  requires k >= 0
  {
    ((k + 1) as real) / ((2 * k + 1) as real)
  }

function DownCoeff(k: int): real
  requires k >= 0
  {
    (k as real) / ((2 * k + 1) as real)
  }
// </vc-helpers>

// <vc-spec>
method LegendreMultiplyByX(c: seq<real>) returns (result: seq<real>)
  requires |c| > 0
  ensures |result| == |c| + 1
// </vc-spec>
// <vc-code>
{
  var m := |c|;
  var r := new real[m + 1];
  var j := 0;
  while j < m + 1
    invariant 0 <= j <= m + 1
    decreases m + 1 - j
  {
    var acc := 0.0;
    if j - 1 >= 0 {
      acc := acc + c[j - 1] * UpCoeff(j - 1);
    }
    if j + 1 < m {
      acc := acc + c[j + 1] * DownCoeff(j + 1);
    }
    r[j] := acc;
    j := j + 1;
  }
  result := r[..];
}
// </vc-code>
