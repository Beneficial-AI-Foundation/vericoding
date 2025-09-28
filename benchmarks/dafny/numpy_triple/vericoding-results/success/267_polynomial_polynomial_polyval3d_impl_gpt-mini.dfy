// <vc-preamble>
// Helper function to compute power of a real number
ghost function Power(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

// Ghost function to evaluate a 3D polynomial at a single point
ghost function EvaluatePolynomial3D(
    x: real, y: real, z: real,
    coeffs: seq<seq<seq<real>>>,
    deg_x: nat, deg_y: nat, deg_z: nat
): real
    requires |coeffs| == deg_x + 1
    requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == deg_y + 1
    requires forall i :: 0 <= i < |coeffs| ==> 
        forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == deg_z + 1
{
    SumOverIndices(x, y, z, coeffs, 0, 0, 0, deg_x, deg_y, deg_z)
}

// Helper ghost function to compute the triple sum
ghost function SumOverIndices(
    x: real, y: real, z: real,
    coeffs: seq<seq<seq<real>>>,
    i: nat, j: nat, k: nat,
    deg_x: nat, deg_y: nat, deg_z: nat
): real
    requires |coeffs| == deg_x + 1
    requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| == deg_y + 1
    requires forall idx :: 0 <= idx < |coeffs| ==> 
        forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| == deg_z + 1
    decreases deg_x - i, deg_y - j, deg_z - k
{
    if i > deg_x then 0.0
    else if j > deg_y then SumOverIndices(x, y, z, coeffs, i + 1, 0, 0, deg_x, deg_y, deg_z)
    else if k > deg_z then SumOverIndices(x, y, z, coeffs, i, j + 1, 0, deg_x, deg_y, deg_z)
    else
        coeffs[i][j][k] * Power(x, i) * Power(y, j) * Power(z, k) + 
        SumOverIndices(x, y, z, coeffs, i, j, k + 1, deg_x, deg_y, deg_z)
}

// Main method for 3D polynomial evaluation
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide noop lemma to satisfy helper section */
lemma Helper_Noop() {
}

// </vc-helpers>

// <vc-spec>
method Polyval3D(
    x: seq<real>, y: seq<real>, z: seq<real>,
    coeffs: seq<seq<seq<real>>>,
    deg_x: nat, deg_y: nat, deg_z: nat
) returns (result: seq<real>)
    requires |x| == |y| == |z|
    requires |coeffs| == deg_x + 1
    requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == deg_y + 1
    requires forall i :: 0 <= i < |coeffs| ==> 
        forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == deg_z + 1
    ensures |result| == |x|
    ensures forall p :: 0 <= p < |result| ==> 
        result[p] == EvaluatePolynomial3D(x[p], y[p], z[p], coeffs, deg_x, deg_y, deg_z)
    ensures deg_x == 0 && deg_y == 0 && deg_z == 0 ==> 
        forall p :: 0 <= p < |result| ==> result[p] == coeffs[0][0][0]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed sequence length usage and corrected power update ordering */
{
  var n := |x|;
  var resArr := new real[n];
  var p := 0;
  while p < n
    invariant 0 <= p <= n
    invariant forall q :: 0 <= q < p ==> resArr[q] == EvaluatePolynomial3D(x[q], y[q], z[q], coeffs, deg_x, deg_y, deg_z)
    decreases n - p
  {
    var xp := x[p]; var yp := y[p]; var zp := z[p];
    var v := 0.0;

    var i := 0;
    var powx := 1.0;
    while i <= deg_x
      invariant 0 <= i <= deg_x + 1
      invariant powx == Power(xp, i)
      invariant v == SumOverIndices(xp, yp, zp, coeffs, 0, 0, 0, deg_x, deg_y, deg_z) - SumOverIndices(xp, yp, zp, coeffs, i, 0, 0, deg_x, deg_y, deg_z)
      decreases deg_x + 1 - i
    {
      var j := 0;
      var powy := 1.0;
      while j <= deg_y
        invariant 0 <= j <= deg_y + 1
        invariant powy == Power(yp, j)
        invariant powx == Power(xp, i)
        invariant v == SumOverIndices(xp, yp, zp, coeffs, 0, 0, 0, deg_x, deg_y, deg_z) - SumOverIndices(xp, yp, zp, coeffs, i, j, 0, deg_x, deg_y, deg_z)
        decreases deg_y + 1 - j
      {
        var k := 0;
        var powz := 1.0;
        while k <= deg_z
          invariant 0 <= k <= deg_z + 1
          invariant powz == Power(zp, k)
          invariant powy == Power(yp, j)
          invariant powx == Power(xp, i)
          invariant v == SumOverIndices(xp, yp, zp, coeffs, 0, 0, 0, deg_x, deg_y, deg_z) - SumOverIndices(xp, yp, zp, coeffs, i, j, k, deg_x, deg_y, deg_z)
          decreases deg_z + 1 - k
        {
          v := v + coeffs[i][j][k] * powx * powy * powz;
          powz := powz * zp;
          k := k + 1;
        }
        powy := powy * yp;
        j := j + 1;
      }
      powx := powx * xp;
      i := i + 1;
    }

    resArr[p] := v;
    p := p + 1;
  }
  result := resArr[..];
}

// </vc-code>
