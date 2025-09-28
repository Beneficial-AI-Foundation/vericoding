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
/* helper modified by LLM (iteration 2): change compiled power to Dafny 4 syntax 'function' (was 'function method') */
function Pow(base: real, exp: nat): real
  decreases exp
{
  if exp == 0 then 1.0 else base * Pow(base, exp - 1)
}

lemma PowEqPower(base: real, exp: nat)
  ensures Pow(base, exp) == Power(base, exp)
  decreases exp
{
  reveal Pow();
  reveal Power();
  if exp != 0 {
    PowEqPower(base, exp - 1);
  }
}

lemma Unfold_EvaluatePolynomial3D(
  x: real, y: real, z: real,
  coeffs: seq<seq<seq<real>>>,
  deg_x: nat, deg_y: nat, deg_z: nat)
  requires |coeffs| == deg_x + 1
  requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == deg_y + 1
  requires forall i :: 0 <= i < |coeffs| ==> forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == deg_z + 1
  ensures EvaluatePolynomial3D(x, y, z, coeffs, deg_x, deg_y, deg_z) ==
          SumOverIndices(x, y, z, coeffs, 0, 0, 0, deg_x, deg_y, deg_z)
{
  reveal EvaluatePolynomial3D();
}

lemma SumOverIndices_StepK(
  x: real, y: real, z: real,
  coeffs: seq<seq<seq<real>>>,
  i: nat, j: nat, k: nat,
  deg_x: nat, deg_y: nat, deg_z: nat)
  requires |coeffs| == deg_x + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| == deg_y + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| == deg_z + 1
  requires i <= deg_x && j <= deg_y && k <= deg_z
  ensures SumOverIndices(x, y, z, coeffs, i, j, k, deg_x, deg_y, deg_z) ==
          coeffs[i][j][k] * Power(x, i) * Power(y, j) * Power(z, k) +
          SumOverIndices(x, y, z, coeffs, i, j, k + 1, deg_x, deg_y, deg_z)
{
  reveal SumOverIndices();
}

lemma SumOverIndices_KDone(
  x: real, y: real, z: real,
  coeffs: seq<seq<seq<real>>>,
  i: nat, j: nat,
  deg_x: nat, deg_y: nat, deg_z: nat)
  requires |coeffs| == deg_x + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| == deg_y + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| == deg_z + 1
  requires i <= deg_x && j <= deg_y
  ensures SumOverIndices(x, y, z, coeffs, i, j, deg_z + 1, deg_x, deg_y, deg_z) ==
          SumOverIndices(x, y, z, coeffs, i, j + 1, 0, deg_x, deg_y, deg_z)
{
  reveal SumOverIndices();
}

lemma SumOverIndices_JDone(
  x: real, y: real, z: real,
  coeffs: seq<seq<seq<real>>>,
  i: nat,
  deg_x: nat, deg_y: nat, deg_z: nat)
  requires |coeffs| == deg_x + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| == deg_y + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| == deg_z + 1
  requires i <= deg_x
  ensures SumOverIndices(x, y, z, coeffs, i, deg_y + 1, 0, deg_x, deg_y, deg_z) ==
          SumOverIndices(x, y, z, coeffs, i + 1, 0, 0, deg_x, deg_y, deg_z)
{
  reveal SumOverIndices();
}

lemma SumOverIndices_IDone(
  x: real, y: real, z: real,
  coeffs: seq<seq<seq<real>>>,
  deg_x: nat, deg_y: nat, deg_z: nat)
  requires |coeffs| == deg_x + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| == deg_y + 1
  requires forall idx :: 0 <= idx < |coeffs| ==> forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| == deg_z + 1
  ensures SumOverIndices(x, y, z, coeffs, deg_x + 1, 0, 0, deg_x, deg_y, deg_z) == 0.0
{
  reveal SumOverIndices();
}

lemma EvaluatePolynomial3D_Deg0EqualsCoeff(
  x: real, y: real, z: real,
  coeffs: seq<seq<seq<real>>>)
  requires |coeffs| == 1
  requires |coeffs[0]| == 1
  requires |coeffs[0][0]| == 1
  ensures EvaluatePolynomial3D(x, y, z, coeffs, 0, 0, 0) == coeffs[0][0][0]
{
  reveal EvaluatePolynomial3D();
  reveal SumOverIndices();
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
/* code modified by LLM (iteration 2): implemented triple-loop evaluation with invariants and helper lemmas */
{
  var n := |x|;
  var res: seq<real> := [];
  var p: nat := 0;
  while p < n
    invariant 0 <= p <= n
    invariant |res| == p
    invariant forall q :: 0 <= q < p ==> res[q] == EvaluatePolynomial3D(x[q], y[q], z[q], coeffs, deg_x, deg_y, deg_z)
    decreases n - p
  {
    assert |y| == |x| && |z| == |x|;
    var xi := x[p];
    var yi := y[p];
    var zi := z[p];

    Unfold_EvaluatePolynomial3D(xi, yi, zi, coeffs, deg_x, deg_y, deg_z);

    var tot: real := 0.0;
    var i: nat := 0;
    while i <= deg_x
      invariant 0 <= i <= deg_x + 1
      invariant tot + SumOverIndices(xi, yi, zi, coeffs, i, 0, 0, deg_x, deg_y, deg_z) == EvaluatePolynomial3D(xi, yi, zi, coeffs, deg_x, deg_y, deg_z)
      decreases if i <= deg_x then deg_x + 1 - i else 0
    {
      var tot_i: real := 0.0;
      var j: nat := 0;
      while j <= deg_y
        invariant 0 <= j <= deg_y + 1
        invariant tot + tot_i + SumOverIndices(xi, yi, zi, coeffs, i, j, 0, deg_x, deg_y, deg_z) == EvaluatePolynomial3D(xi, yi, zi, coeffs, deg_x, deg_y, deg_z)
        decreases if j <= deg_y then deg_y + 1 - j else 0
      {
        var tot_k: real := 0.0;
        var k: nat := 0;
        while k <= deg_z
          invariant 0 <= k <= deg_z + 1
          invariant tot + tot_i + tot_k + SumOverIndices(xi, yi, zi, coeffs, i, j, k, deg_x, deg_y, deg_z) == EvaluatePolynomial3D(xi, yi, zi, coeffs, deg_x, deg_y, deg_z)
          decreases if k <= deg_z then deg_z + 1 - k else 0
        {
          SumOverIndices_StepK(xi, yi, zi, coeffs, i, j, k, deg_x, deg_y, deg_z);
          PowEqPower(xi, i);
          PowEqPower(yi, j);
          PowEqPower(zi, k);
          var t := coeffs[i][j][k] * Pow(xi, i) * Pow(yi, j) * Pow(zi, k);
          tot_k := tot_k + t;
          k := k + 1;
        }
        SumOverIndices_KDone(xi, yi, zi, coeffs, i, j, deg_x, deg_y, deg_z);
        tot_i := tot_i + tot_k;
        j := j + 1;
      }
      SumOverIndices_JDone(xi, yi, zi, coeffs, i, deg_x, deg_y, deg_z);
      tot := tot + tot_i;
      i := i + 1;
    }
    SumOverIndices_IDone(xi, yi, zi, coeffs, deg_x, deg_y, deg_z);

    res := res + [tot];
    p := p + 1;
  }
  result := res;
}
// </vc-code>
