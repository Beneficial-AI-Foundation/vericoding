// <vc-preamble>
// Helper function to compute dot product of two sequences
function DotProduct(a: seq<real>, b: seq<real>): real
  requires |a| == |b|
{
  if |a| == 0 then 0.0
  else a[0] * b[0] + DotProduct(a[1..], b[1..])
}

// Helper function to extract column j from matrix B
function GetColumn(B: seq<seq<real>>, j: nat): seq<real>
  requires forall i :: 0 <= i < |B| ==> j < |B[i]|
{
  seq(|B|, i requires 0 <= i < |B| => B[i][j])
}

// Helper predicate to check if matrix has valid dimensions
predicate IsValidMatrix(M: seq<seq<real>>, rows: nat, cols: nat)
{
  |M| == rows && 
  (forall i :: 0 <= i < |M| ==> |M[i]| == cols)
}

// Matrix multiplication method
// </vc-preamble>

// <vc-helpers>
lemma LengthOfGetColumn(B: seq<seq<real>>, j: nat)
  requires forall i :: 0 <= i < |B| ==> j < |B[i]|
  ensures |GetColumn(B, j)| == |B|
{
}

lemma ColumnIndexValid(B: seq<seq<real>>, j: nat)
  requires |B| > 0
  requires forall i :: 0 <= i < |B| ==> |B[i]| == |B[0]|
  requires j < |B[0]|
  ensures forall i :: 0 <= i < |B| ==> j < |B[i]|
{
}
// </vc-helpers>

// <vc-spec>
method MatMul(A: seq<seq<real>>, B: seq<seq<real>>) returns (C: seq<seq<real>>)
  // Input matrices must be well-formed and compatible for multiplication
  requires |A| > 0 && |B| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| > 0
  requires forall i :: 0 <= i < |B| ==> |B[i]| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |B|  // A columns == B rows
  requires forall i :: 0 <= i < |B| ==> |B[i]| == |B[0]|  // B has consistent column count
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|  // A has consistent column count
  
  // Output matrix has correct dimensions and each element is computed as dot product
  ensures |C| == |A|  // Result has same number of rows as A
  ensures forall i :: 0 <= i < |C| ==> |C[i]| == |B[0]|  // Result has same number of columns as B
  ensures forall i, j :: 0 <= i < |C| && 0 <= j < |C[i]| ==> 
    C[i][j] == DotProduct(A[i], GetColumn(B, j))
// </vc-spec>
// <vc-code>
{
  C := seq(|A|, i requires 0 <= i < |A| =>
           seq(|B[0]|, j requires 0 <= j < |B[0]| =>
             DotProduct(A[i], GetColumn(B, j))
           )
         );
}
// </vc-code>
