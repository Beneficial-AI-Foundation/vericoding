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
{
  result := [];
  var p := 0;
  while p < |x|
    invariant 0 <= p <= |x|
    invariant |result| == p
    invariant forall q :: 0 <= q < p ==> result[q] == EvaluatePolynomial3D(x[q], y[q], z[q], coeffs, deg_x, deg_y, deg_z)
  {
    var sum := 0.0;
    var i := 0;
    while i <= deg_x
      invariant 0 <= i <= deg_x + 1
      invariant sum == SumOverIndices(x[p], y[p], z[p], coeffs, 0, 0, 0, deg_x, deg_y, deg_z) - SumOverIndices(x[p], y[p], z[p], coeffs, i, 0, 0, deg_x, deg_y, deg_z)
    {
      var j := 0;
      while j <= deg_y
        invariant 0 <= j <= deg_y + 1
        invariant sum == SumOverIndices(x[p], y[p], z[p], coeffs, 0, 0, 0, deg_x, deg_y, deg_z) - SumOverIndices(x[p], y[p], z[p], coeffs, i, j, 0, deg_x, deg_y, deg_z)
      {
        var k := 0;
        while k <= deg_z
          invariant 0 <= k <= deg_z + 1
          invariant sum == SumOverIndices(x[p], y[p], z[p], coeffs, 0, 0, 0, deg_x, deg_y, deg_z) - SumOverIndices(x[p], y[p], z[p], coeffs, i, j, k, deg_x, deg_y, deg_z)
        {
          var x_pow := 1.0;
          var xi := 0;
          while xi < i
            invariant 0 <= xi <= i
            invariant x_pow == Power(x[p], xi)
          {
            x_pow := x_pow * x[p];
            xi := xi + 1;
          }
          var y_pow := 1.0;
          var yi := 0;
          while yi < j
            invariant 0 <= yi <= j
            invariant y_pow == Power(y[p], yi)
          {
            y_pow := y_pow * y[p];
            yi := yi + 1;
          }
          var z_pow := 1.0;
          var zi := 0;
          while zi < k
            invariant 0 <= zi <= k
            invariant z_pow == Power(z[p], zi)
          {
            z_pow := z_pow * z[p];
            zi := zi + 1;
          }
          sum := sum + coeffs[i][j][k] * x_pow * y_pow * z_pow;
          k := k + 1;
        }
        j := j + 1;
      }
      i := i + 1;
    }
    result := result + [sum];
    p := p + 1;
  }
}
// </vc-code>
