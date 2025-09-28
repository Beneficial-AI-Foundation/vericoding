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
  /* code modified by LLM (iteration 5): [use nested loops to avoid non-linear arithmetic in invariants] */
  ret := seq(m * n, _ => 0);
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |ret| == m * n
    invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> ret[r * n + c] == MatrixGet(arr, r, c)
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |ret| == m * n
      invariant forall r, c :: 0 <= r < i && 0 <= c < n ==> ret[r * n + c] == MatrixGet(arr, r, c)
      invariant forall c :: 0 <= c < j ==> ret[i * n + c] == MatrixGet(arr, i, c)
    {
      var k := i * n + j;
      ret := ret[k := MatrixGet(arr, i, j)];
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
