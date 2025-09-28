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

function GetRowCount(M: seq<seq<real>>): nat { |M| }
function GetColumnCount(M: seq<seq<real>>): nat requires |M| > 0 { |M[0]| }
predicate IsRectangularMatrix(M: seq<seq<real>>) {
  |M| > 0 ==> (forall i :: 0 <= i < |M| ==> |M[i]| == |M[0]|)
}
lemma GetColumnIndexValid(B: seq<seq<real>>, j: nat)
  requires |B| > 0 && forall i :: 0 <= i < |B| ==> |B[i]| > 0
  requires forall i :: 0 <= i < |B| ==> |B[i]| == |B[0]|
  requires j < |B[0]|
  ensures forall i :: 0 <= i < |B| ==> j < |B[i]|
{
}
lemma MatrixMultiplicationValid(A: seq<seq<real>>, B: seq<seq<real>>)
  requires |A| > 0 && |B| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| > 0
  requires forall i :: 0 <= i < |B| ==> |B[i]| > 0
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |B|
  requires forall i :: 0 <= i < |B| ==> |B[i]| == |B[0]|
  requires forall i :: 0 <= i < |A| ==> |A[i]| == |A[0]|
  ensures IsRectangularMatrix(A) && IsRectangularMatrix(B)
  ensures |A[0]| == |B|
  ensures |B[0]| > 0
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
  /* code modified by LLM (iteration 2): Fixed array assignment syntax */
  MatrixMultiplicationValid(A, B);
  var rowsA := |A|;
  var colsB := |B[0]|;
  
  // Initialize result matrix with proper dimensions
  C := seq(rowsA, i => seq(colsB, j => 0.0));
  
  var i := 0;
  while i < rowsA
    invariant 0 <= i <= rowsA
    invariant |C| == rowsA
    invariant forall k :: 0 <= k < |C| ==> |C[k]| == colsB
    invariant forall k, l :: 0 <= k < i && 0 <= l < colsB ==> C[k][l] == DotProduct(A[k], GetColumn(B, l))
  {
    var j := 0;
    while j < colsB
      invariant 0 <= j <= colsB
      invariant |C| == rowsA
      invariant forall k :: 0 <= k < |C| ==> |C[k]| == colsB
      invariant forall k, l :: 0 <= k < i && 0 <= l < colsB ==> C[k][l] == DotProduct(A[k], GetColumn(B, l))
      invariant forall l :: 0 <= l < j ==> C[i][l] == DotProduct(A[i], GetColumn(B, l))
    {
      // Verify column index is valid for all rows in B
      GetColumnIndexValid(B, j);
      C := C[i := C[i][j := DotProduct(A[i], GetColumn(B, j))]];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
