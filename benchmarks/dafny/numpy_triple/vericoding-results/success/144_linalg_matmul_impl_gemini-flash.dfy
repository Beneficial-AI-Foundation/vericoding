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
/* helper modified by LLM (iteration 3): The previous implementation of helper_DotProductLength was incorrect or incomplete, leading to verification errors. This updated version directly uses the DotProduct function without needing a calc block to show an identity, assuming DotProduct is already correct. */
lemma helper_DotProductLength(a: seq<real>, b: seq<real>)
  requires |a| == |b|
  ensures DotProduct(a, b) == DotProduct(a, b){}
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
/* code modified by LLM (iteration 3): Fixed compilation errors related to sequence initialization and assignment. The errors indicated issues with `new seq` syntax and assignment incompatibilities between `seq` and `array?<?}`. The corrected code initializes sequences using constructor `seq<real>` for the inner rows and then builds the outer `C_var` sequence element by element using `C_var := C_var + [row_i]`. Array-like updates are avoided. */
{
  var rowsA := |A|;
  var colsB := |B[0]|;

  var C_var: seq<seq<real>> := [];

  var i := 0;
  while i < rowsA
    invariant 0 <= i <= rowsA
    invariant |C_var| == i
    invariant forall x :: 0 <= x < i ==> |C_var[x]| == colsB
    invariant forall x :: 0 <= x < i ==> forall y :: 0 <= y < colsB ==> C_var[x][y] == DotProduct(A[x], GetColumn(B, y))
  {
    var row_i: seq<real> := [];
    var j := 0;
    while j < colsB
      invariant 0 <= j <= colsB
      invariant |row_i| == j
      invariant forall y :: 0 <= y < j ==> row_i[y] == DotProduct(A[i], GetColumn(B, y))
    {
      row_i := row_i + [DotProduct(A[i], GetColumn(B, j))];
      j := j + 1;
    }
    C_var := C_var + [row_i];
    i := i + 1;
  }
  C := C_var;
}
// </vc-code>
