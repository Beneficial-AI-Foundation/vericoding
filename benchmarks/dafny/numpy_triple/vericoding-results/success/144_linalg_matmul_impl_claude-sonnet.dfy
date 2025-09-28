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
lemma DotProductWellDefined(a: seq<real>, b: seq<real>, col: seq<real>)
  requires |a| == |b|
  requires |b| == |col|
  ensures |a| == |col|
{
}

lemma GetColumnLength(B: seq<seq<real>>, j: nat)
  requires |B| > 0
  requires forall i :: 0 <= i < |B| ==> j < |B[i]|
  requires forall i :: 0 <= i < |B| ==> |B[i]| == |B[0]|
  ensures |GetColumn(B, j)| == |B|
{
}

lemma GetColumnValid(B: seq<seq<real>>, j: nat)
  requires |B| > 0
  requires forall i :: 0 <= i < |B| ==> |B[i]| > 0
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
  C := [];
  var i := 0;
  while i < |A|
    invariant 0 <= i <= |A|
    invariant |C| == i
    invariant forall k :: 0 <= k < i ==> |C[k]| == |B[0]|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |B[0]| ==> C[k][j] == DotProduct(A[k], GetColumn(B, j))
  {
    var row := [];
    var j := 0;
    while j < |B[0]|
      invariant 0 <= j <= |B[0]|
      invariant |row| == j
      invariant forall l :: 0 <= l < j ==> row[l] == DotProduct(A[i], GetColumn(B, l))
    {
      GetColumnValid(B, j);
      GetColumnLength(B, j);
      DotProductWellDefined(A[i], GetColumn(B, j), GetColumn(B, j));
      var dotProd := DotProduct(A[i], GetColumn(B, j));
      row := row + [dotProd];
      j := j + 1;
    }
    C := C + [row];
    i := i + 1;
  }
}
// </vc-code>
