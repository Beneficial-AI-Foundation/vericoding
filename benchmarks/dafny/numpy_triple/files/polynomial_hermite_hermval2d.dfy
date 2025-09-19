// <vc-preamble>
// Helper function to compute Hermite polynomials using recurrence relation
ghost function HermitePolynomial(n: nat, x: real): real
  decreases n
{
  if n == 0 then 1.0
  else if n == 1 then 2.0 * x
  else 2.0 * x * HermitePolynomial(n - 1, x) - 2.0 * (n - 1) as real * HermitePolynomial(n - 2, x)
}

// Helper function to compute the 2D Hermite series evaluation at a single point
ghost function Hermval2DPoint(x: real, y: real, c: seq<seq<real>>): real
  requires |c| > 0 ==> forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|
{
  if |c| == 0 || (|c| > 0 && |c[0]| == 0) then 0.0
  else
    var rows := |c|;
    var cols := |c[0]|;
    var sum := 0.0;
    // Sum over all i,j: c[i][j] * H_i(x) * H_j(y)
    sum + (
      var terms := seq(rows, i => seq(cols, j => c[i][j] * HermitePolynomial(i, x) * HermitePolynomial(j, y)));
      SumMatrix(terms)
    )
}

// Helper function to sum all elements in a 2D matrix
ghost function SumMatrix(matrix: seq<seq<real>>): real
{
  if |matrix| == 0 then 0.0
  else SumSequence(matrix[0]) + SumMatrix(matrix[1..])
}

// Helper function to sum elements in a sequence
ghost function SumSequence(s: seq<real>): real
{
  if |s| == 0 then 0.0
  else s[0] + SumSequence(s[1..])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Hermval2D(x: seq<real>, y: seq<real>, c: seq<seq<real>>) returns (result: seq<real>)
  requires |x| == |y|  // x and y must have same length
  requires |c| > 0 ==> forall i :: 0 <= i < |c| ==> |c[i]| == |c[0]|  // all rows same length
  ensures |result| == |x|  // result has same length as input vectors
  ensures forall k :: 0 <= k < |result| ==> 
    result[k] == Hermval2DPoint(x[k], y[k], c)  // each result element is the 2D evaluation
  ensures |c| == 0 || (|c| > 0 && |c[0]| == 0) ==> 
    forall k :: 0 <= k < |result| ==> result[k] == 0.0  // empty coefficients give zero
  // Bilinearity property: linear in coefficients
  ensures forall c1: seq<seq<real>>, c2: seq<seq<real>>, a: real, b: real ::
    {:trigger Hermval2DPoint(x[0], y[0], c1), Hermval2DPoint(x[0], y[0], c2)}
    (|c1| == |c| && |c2| == |c| && 
     (|c| > 0 ==> |c1[0]| == |c[0]| && |c2[0]| == |c[0]|) &&
     (forall i :: 0 <= i < |c1| ==> |c1[i]| == |c1[0]|) &&
     (forall i :: 0 <= i < |c2| ==> |c2[i]| == |c2[0]|)) ==>
    var c_combined := seq(|c|, i => seq(if |c| > 0 then |c[0]| else 0, j => a * c1[i][j] + b * c2[i][j]));
    forall k :: 0 <= k < |result| ==> 
      Hermval2DPoint(x[k], y[k], c_combined) == 
      a * Hermval2DPoint(x[k], y[k], c1) + b * Hermval2DPoint(x[k], y[k], c2)
  // Separability for degenerate cases
  ensures |c| == 1 && |c| > 0 && |c[0]| > 0 ==>
    forall k :: 0 <= k < |result| ==> 
      result[k] == SumSequence(seq(|c[0]|, j => c[0][j] * HermitePolynomial(j, y[k])))
  ensures |c| > 0 && |c[0]| == 1 ==>
    forall k :: 0 <= k < |result| ==> 
      result[k] == SumSequence(seq(|c|, i => c[i][0] * HermitePolynomial(i, x[k])))
  // Hermite polynomial properties in the specification
  ensures forall n: nat, x_val: real :: 
    {:trigger HermitePolynomial(n, x_val)}
    HermitePolynomial(0, x_val) == 1.0 &&
    HermitePolynomial(1, x_val) == 2.0 * x_val &&
    (n >= 2 ==> (HermitePolynomial(n, x_val) == 
      2.0 * x_val * HermitePolynomial(n - 1, x_val) - 
      2.0 * (n - 1) as real * HermitePolynomial(n - 2, x_val)))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
