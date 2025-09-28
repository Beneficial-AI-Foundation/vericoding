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
/* helper modified by LLM (iteration 5): element accessor mapping linear index to matrix element */
function RavelAt(arr: Matrix<int>, m: int, n: int, k: int): int
  requires m > 0 && n > 0 && 0 <= k < m * n
{
  MatrixGet(arr, k / n, k % n)
}

/* helper modified by LLM (iteration 5): lemma proving division/mod properties for linear indexing */
lemma DivModLinearIndex(m: int, n: int, k: int)
  requires m > 0 && n > 0 && 0 <= k < m * n
  ensures 0 <= k / n < m && 0 <= k % n < n
  ensures k == (k / n) * n + k % n
{
  // Dafny can discharge these arithmetic facts automatically
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
  /* code modified by LLM (iteration 5): construct flattened sequence using comprehension */
  ret := seq k | 0 <= k < m * n :: RavelAt(arr, m, n, k);
}

// </vc-code>
