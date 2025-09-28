// <vc-preamble>
// Method to compute the scaled companion matrix of Hermite polynomial coefficients
// Ghost function for square root (assumed to exist in the real number domain)
function Sqrt(x: real): real
  requires x >= 0.0
  ensures Sqrt(x) * Sqrt(x) == x
{
  assume {:axiom} false; 
  0.0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Define matrix entry following Hermite companion structure */
function Entry(c: seq<real>, i: int, j: int): real
  requires |c| >= 2
  requires c[|c| - 1] != 0.0
  requires 0 <= i < |c| - 1
  requires 0 <= j < |c| - 1
{
  if j == |c| - 2 then
    -c[i] / (2.0 * c[|c| - 1]) * (if i == |c| - 2 then Sqrt(0.5 * ((|c| - 2) as real)) else 1.0)
  else if j == i + 1 || i == j + 1 then
    Sqrt(0.5 * (((if j == i + 1 then i else j) as real) + 1.0))
  else
    0.0
}

/* helper modified by LLM (iteration 2): Build a row as a prefix using recursion */
function RowPrefix(c: seq<real>, i: int, k: nat): seq<real>
  requires |c| >= 2
  requires c[|c| - 1] != 0.0
  requires 0 <= i < |c| - 1
  requires k <= |c| - 1
  decreases k
  ensures |RowPrefix(c, i, k)| == k
  ensures forall j :: 0 <= j < k ==> RowPrefix(c, i, k)[j] == Entry(c, i, j)
{
  if k == 0 then
    []
  else
    RowPrefix(c, i, k - 1) + [Entry(c, i, k - 1)]
}

/* helper modified by LLM (iteration 2): Expose full row of length |c|-1 */
function MakeRow(c: seq<real>, i: int): seq<real>
  requires |c| >= 2
  requires c[|c| - 1] != 0.0
  requires 0 <= i < |c| - 1
  ensures |MakeRow(c, i)| == |c| - 1
  ensures forall j :: 0 <= j < |c| - 1 ==> MakeRow(c, i)[j] == Entry(c, i, j)
{
  RowPrefix(c, i, |c| - 1)
}

/* helper modified by LLM (iteration 2): Build matrix as a prefix of rows using recursion */
function MatPrefix(c: seq<real>, k: nat): seq<seq<real>>
  requires |c| >= 2
  requires c[|c| - 1] != 0.0
  requires k <= |c| - 1
  decreases k
  ensures |MatPrefix(c, k)| == k
  ensures forall i :: 0 <= i < k ==> MatPrefix(c, k)[i] == MakeRow(c, i)
{
  if k == 0 then
    []
  else
    MatPrefix(c, k - 1) + [MakeRow(c, k - 1)]
}

/* helper modified by LLM (iteration 2): Expose full matrix of size (|c|-1) x (|c|-1) */
function MakeMatrix(c: seq<real>): seq<seq<real>>
  requires |c| >= 2
  requires c[|c| - 1] != 0.0
  ensures |MakeMatrix(c)| == |c| - 1
  ensures forall i :: 0 <= i < |c| - 1 ==> |MakeMatrix(c)[i]| == |c| - 1
  ensures forall i, j :: 0 <= i < |c| - 1 && 0 <= j < |c| - 1 ==> MakeMatrix(c)[i][j] == Entry(c, i, j)
{
  MatPrefix(c, |c| - 1)
}
// </vc-helpers>

// <vc-spec>
method HermCompanion(c: seq<real>) returns (mat: seq<seq<real>>)
  // Input must have at least 2 coefficients
  requires |c| >= 2
  // Leading coefficient must be non-zero
  requires c[|c|-1] != 0.0
  
  // Matrix dimensions are (n+1) x (n+1) where n = |c| - 2
  ensures |mat| == |c| - 1
  ensures forall i :: 0 <= i < |mat| ==> |mat[i]| == |c| - 1
  
  // Super-diagonal elements: mat[k][k+1] = sqrt(0.5 * (k+1)) for k = 0 to n-1
  ensures forall k {:trigger mat[k][k+1]} :: 0 <= k < |c| - 2 ==> 
    mat[k][k+1] == Sqrt(0.5 * (k as real + 1.0))
  
  // Sub-diagonal elements: mat[k+1][k] = sqrt(0.5 * (k+1)) for k = 0 to n-1  
  ensures forall k {:trigger mat[k+1][k]} :: 0 <= k < |c| - 2 ==> 
    mat[k+1][k] == Sqrt(0.5 * (k as real + 1.0))
  
  // Main diagonal is zero except possibly last row
  ensures forall i :: 0 <= i < |c| - 1 ==> 
    (i != |c| - 2) ==> mat[i][i] == 0.0
  
  // All other entries except last column are zero
  ensures forall i, j :: 0 <= i < |c| - 1 && 0 <= j < |c| - 2 ==>
    (i != j && i != j + 1 && i + 1 != j) ==> mat[i][j] == 0.0
  
  // Last column contains scaled coefficients
  ensures forall i :: 0 <= i < |c| - 1 ==>
    mat[i][|c| - 2] == -c[i] / (2.0 * c[|c| - 1]) * 
    (if i == |c| - 2 then Sqrt(0.5 * ((|c| - 2) as real)) else 1.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Construct matrix using verified helper MakeMatrix */
  mat := MakeMatrix(c);
}
// </vc-code>
