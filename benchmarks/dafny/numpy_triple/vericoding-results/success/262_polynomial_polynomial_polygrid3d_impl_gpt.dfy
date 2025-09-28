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
/* helper modified by LLM (iteration 2): simple minimum function for reals */
function minReal(a: real, b: real): real
{
  if a <= b then a else b
}

/* helper modified by LLM (iteration 2): predicate to check rectangular 3D sequence */
predicate IsRectangular3D(c: seq<seq<seq<real>>>)
{
  |c| > 0 &&
  (forall i :: 0 <= i < |c| ==> |c[i]| > 0) &&
  (forall i :: 0 <= i < |c| ==> forall j :: 0 <= j < |c[i]| ==> |c[i][j]| > 0) &&
  (forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|) &&
  (forall i :: 0 <= i < |c| ==> forall j :: 0 <= j < |c[i]| ==> |c[i][j]| == |c[0][0]|)
}
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
  /* code modified by LLM (iteration 2): Build 3D result via nested loops to avoid comprehension parse issues */
  var res: seq<seq<seq<real>>> := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |res| == i
    invariant forall ii :: 0 <= ii < |res| ==> |res[ii]| == |y|
    invariant forall ii :: 0 <= ii < |res| ==> forall jj :: 0 <= jj < |res[ii]| ==> |res[ii][jj]| == |z|
    invariant forall ii :: 0 <= ii < |res| ==> forall jj :: 0 <= jj < |res[ii]| ==> forall kk :: 0 <= kk < |res[ii][jj]| ==> res[ii][jj][kk] == EvaluatePolynomial3D(x[ii], y[jj], z[kk], c)
  {
    var row: seq<seq<real>> := [];
    var j := 0;
    while j < |y|
      invariant 0 <= j <= |y|
      invariant |row| == j
      invariant forall jj :: 0 <= jj < |row| ==> |row[jj]| == |z|
      invariant forall jj :: 0 <= jj < |row| ==> forall kk :: 0 <= kk < |row[jj]| ==> row[jj][kk] == EvaluatePolynomial3D(x[i], y[jj], z[kk], c)
    {
      var col: seq<real> := [];
      var k := 0;
      while k < |z|
        invariant 0 <= k <= |z|
        invariant |col| == k
        invariant forall kk :: 0 <= kk < |col| ==> col[kk] == EvaluatePolynomial3D(x[i], y[j], z[kk], c)
      {
        col := col + [EvaluatePolynomial3D(x[i], y[j], z[k], c)];
        k := k + 1;
      }
      row := row + [col];
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
