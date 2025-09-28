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
function IndexToRowCol(index: int, n: int): (int, int)
  requires n > 0
  ensures var (i, j) := IndexToRowCol(index, n); index == i * n + j && 0 <= j < n
{
  (index / n, index % n)
}

lemma IndexToRowColValidRange(index: int, n: int, m: int)
  requires n > 0
  requires m > 0
  requires 0 <= index < m * n
  ensures var (i, j) := IndexToRowCol(index, n); 0 <= i < m && 0 <= j < n
{
  /* helper modified by LLM (iteration 4): Added range validation lemma with proper postcondition */
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
  /* code modified by LLM (iteration 4): Simplified direct sequence construction without helper lemma timing out */
  var size := m * n;
  ret := [];
  var idx := 0;
  
  while idx < size
    invariant 0 <= idx <= size
    invariant |ret| == idx
    invariant forall k :: 0 <= k < idx ==> 
             ret[k] == MatrixGet(arr, k / n, k % n)
  {
    ret := ret + [MatrixGet(arr, idx / n, idx % n)];
    idx := idx + 1;
  }
}
// </vc-code>
