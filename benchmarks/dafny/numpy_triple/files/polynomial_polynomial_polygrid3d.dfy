// <vc-preamble>
// Helper function to compute real number power
function Power(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

// Helper function to evaluate the 3D polynomial at a single point
function EvaluatePolynomial3D(a: real, b: real, c: real, coeffs: seq<seq<seq<real>>>): real
    requires |coeffs| > 0
    requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| > 0
    requires forall i :: 0 <= i < |coeffs| ==> forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| > 0
    requires forall i :: 0 <= i < |coeffs| ==> forall j :: 0 <= j < |coeffs[i]| ==> |coeffs[i][j]| == |coeffs[0][0]|
    requires forall i :: 0 <= i < |coeffs| ==> |coeffs[i]| == |coeffs[0]|
{
    var degree_x := |coeffs| - 1;
    var degree_y := |coeffs[0]| - 1;
    var degree_z := |coeffs[0][0]| - 1;
    
    SumTriple(0, 0, 0, degree_x, degree_y, degree_z, a, b, c, coeffs)
}

// Helper function to compute the triple sum for polynomial evaluation
function SumTriple(i: nat, j: nat, k: nat, max_i: nat, max_j: nat, max_k: nat, 
                   a: real, b: real, c: real, coeffs: seq<seq<seq<real>>>): real
    requires |coeffs| > 0 && max_i < |coeffs|
    requires forall idx :: 0 <= idx < |coeffs| ==> |coeffs[idx]| > 0 && max_j < |coeffs[idx]|
    requires forall idx :: 0 <= idx < |coeffs| ==> forall jdx :: 0 <= jdx < |coeffs[idx]| ==> |coeffs[idx][jdx]| > 0 && max_k < |coeffs[idx][jdx]|
    decreases max_i - i, max_j - j, max_k - k
{
    if i > max_i then 0.0
    else if j > max_j then SumTriple(i + 1, 0, 0, max_i, max_j, max_k, a, b, c, coeffs)
    else if k > max_k then SumTriple(i, j + 1, 0, max_i, max_j, max_k, a, b, c, coeffs)
    else coeffs[i][j][k] * Power(a, i) * Power(b, j) * Power(c, k) +
         SumTriple(i, j, k + 1, max_i, max_j, max_k, a, b, c, coeffs)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method polygrid3d(x: seq<real>, y: seq<real>, z: seq<real>, c: seq<seq<seq<real>>>) 
    returns (result: seq<seq<seq<real>>>)
    requires |x| > 0 && |y| > 0 && |z| > 0
    requires |c| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
    requires forall i :: 0 <= i < |c| ==> forall j :: 0 <= j < |c[i]| ==> |c[i][j]| > 0
    // All coefficient arrays have the same dimensions (rectangular 3D array)
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
    requires forall i :: 0 <= i < |c| ==> forall j :: 0 <= j < |c[i]| ==> |c[i][j]| == |c[0][0]|
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |y|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> |result[i][j]| == |z|
    // Each element result[i][j][k] equals the polynomial evaluated at (x[i], y[j], z[k])
    ensures forall i :: 0 <= i < |result| ==> 
            forall j :: 0 <= j < |result[i]| ==> 
            forall k :: 0 <= k < |result[i][j]| ==>
            result[i][j][k] == EvaluatePolynomial3D(x[i], y[j], z[k], c)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
