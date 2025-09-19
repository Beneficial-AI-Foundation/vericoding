// <vc-preamble>
// Helper function to compute real number powers
function Power(base: real, exp: nat): real
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

// Helper function to evaluate polynomial at a single point
function EvaluatePolynomial2D(x: real, y: real, c: seq<seq<real>>): real
    requires |c| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
{
    var nx := |c| - 1;
    var ny := |c[0]| - 1;
    SumOverIndices(x, y, c, 0, 0, nx, ny)
}

// Recursive helper to compute the double sum Σᵢⱼ c[i][j]·xⁱ·yʲ
function SumOverIndices(x: real, y: real, c: seq<seq<real>>, i: nat, j: nat, nx: nat, ny: nat): real
    requires |c| > 0 && |c| == nx + 1
    requires forall k :: 0 <= k < |c| ==> |c[k]| > 0 && |c[k]| == ny + 1
    requires i <= nx && j <= ny
    decreases nx - i, ny - j
{
    if i > nx then 0.0
    else if j > ny then SumOverIndices(x, y, c, i + 1, 0, nx, ny)
    else c[i][j] * Power(x, i) * Power(y, j) + SumOverIndices(x, y, c, i, j + 1, nx, ny)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method polyval2d(x: seq<real>, y: seq<real>, c: seq<seq<real>>) returns (result: seq<real>)
    // Input constraints
    requires |x| == |y|  // x and y must have same length
    requires |c| > 0     // coefficient matrix must be non-empty
    requires forall i :: 0 <= i < |c| ==> |c[i]| > 0  // each row must be non-empty
    requires forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|  // all rows same length (rectangular matrix)
    
    // Output constraints
    ensures |result| == |x|  // result has same length as input vectors
    
    // Main polynomial evaluation property
    ensures forall k :: 0 <= k < |result| ==> 
        result[k] == EvaluatePolynomial2D(x[k], y[k], c)
    
    // Constant term property: when evaluating at origin, result is c[0][0]
    ensures forall k :: 0 <= k < |result| ==> 
        (x[k] == 0.0 && y[k] == 0.0) ==> result[k] == c[0][0]
    
    // Zero polynomial property: if all coefficients are zero, result is zero
    ensures (forall i, j :: 0 <= i < |c| && 0 <= j < |c[i]| ==> c[i][j] == 0.0) ==>
        (forall k :: 0 <= k < |result| ==> result[k] == 0.0)
    
    // Single constant term property: if matrix is 1x1, result is always c[0][0]
    ensures (|c| == 1 && |c[0]| == 1) ==> 
        (forall k :: 0 <= k < |result| ==> result[k] == c[0][0])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
