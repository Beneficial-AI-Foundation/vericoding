// <vc-preamble>
/* Matrix type definition: function from row,col indices to values */
type Matrix<T> = int -> int -> T

/* Get matrix element at position (i,j) */
function MatrixGet<T>(mat: Matrix<T>, i: int, j: int): T
{
    mat(i)(j)
}

/* Matrix size helper */
function MatrixSize(m: int, n: int): int
{
    m * n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to help verify index correspondence */
lemma IndexCorrespondence(i: int, j: int, n: int, idx: int)
  requires n > 0
  requires 0 <= i && 0 <= j < n
  requires idx == i * n + j
  ensures idx / n == i
  ensures idx % n == j
{
  // Dafny can prove this automatically
}
// </vc-helpers>

// <vc-spec>
method Ravel(arr: Matrix<int>, m: int, n: int) returns (ret: seq<int>)
    requires m > 0 && n > 0
    ensures |ret| == m * n
    ensures forall i, j :: 0 <= i < m && 0 <= j < n && 0 <= i * n + j < |ret| ==> 
            ret[i * n + j] == MatrixGet(arr, i, j)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): simplified invariants to avoid verification timeout */
  ret := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |ret| == i * n
    invariant forall row, col :: 0 <= row < i && 0 <= col < n ==>
            ret[row * n + col] == MatrixGet(arr, row, col)
  {
    var j := 0;
    while j < n
      invariant 0 <= i < m
      invariant 0 <= j <= n
      invariant |ret| == i * n + j
      invariant forall row, col :: 0 <= row < i && 0 <= col < n ==>
              ret[row * n + col] == MatrixGet(arr, row, col)
      invariant forall col :: 0 <= col < j ==>
              ret[i * n + col] == MatrixGet(arr, i, col)
    {
      ret := ret + [MatrixGet(arr, i, j)];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
