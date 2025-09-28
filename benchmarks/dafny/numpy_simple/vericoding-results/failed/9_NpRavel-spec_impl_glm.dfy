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
lemma DivMod(i: int, j: int, n: int)
    requires n > 0 && 0 <= j < n
    ensures (i * n + j) / n == i && (i * n + j) % n == j
{
    assert n * i <= n * i + j < n * (i+1);
    assert (n * i + j) / n == i;
    assert (n * i + j) % n == j;
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
  /* code modified by LLM (iteration 5): fixed sequence comprehension syntax */
  ret := seq(k | 0 <= k < m * n :: MatrixGet(arr, k / n, k % n));
}
// </vc-code>
