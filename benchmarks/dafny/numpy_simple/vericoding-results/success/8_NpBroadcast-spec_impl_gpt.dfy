// <vc-preamble>
/* Matrix type definition - represents an m×n matrix */
datatype Matrix<T> = Matrix(
    data: seq<seq<T>>,
    rows: int,
    cols: int
)

predicate MatrixWf<T>(m: Matrix<T>)
{
    && |m.data| == m.rows
    && (forall i :: 0 <= i < |m.data| ==> |m.data[i]| == m.cols)
}

function MatrixIndex<T>(m: Matrix<T>, i: int, j: int): T
    requires 0 <= i < m.rows && 0 <= j < m.cols && MatrixWf(m)
{
    m.data[i][j]
}

function MatrixSize<T>(m: Matrix<T>): int
{
    m.rows * m.cols
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): recursive replicate without comprehensions */
function Replicate(x: int, n: int): seq<int>
  requires 0 <= n
  ensures |Replicate(x, n)| == n
  ensures forall i :: 0 <= i < n ==> Replicate(x, n)[i] == x
  decreases n
{
  if n == 0 then [] else [x] + Replicate(x, n - 1)
}

/* helper modified by LLM (iteration 2): build rows recursively to avoid comprehensions */
function BuildRowsFromA_Upto(a: seq<int>, cols: int, k: int): seq<seq<int>>
  requires 0 <= k <= |a| && 0 <= cols
  ensures |BuildRowsFromA_Upto(a, cols, k)| == k
  ensures forall i :: 0 <= i < k ==> |BuildRowsFromA_Upto(a, cols, k)[i]| == cols
  ensures forall i, j :: 0 <= i < k && 0 <= j < cols ==> BuildRowsFromA_Upto(a, cols, k)[i][j] == a[i]
  decreases k
{
  if k == 0 then []
  else BuildRowsFromA_Upto(a, cols, k - 1) + [Replicate(a[k - 1], cols)]
}

/* helper modified by LLM (iteration 2): wrapper preserving original signature */
function BuildRowsFromA(a: seq<int>, rows: int, cols: int): seq<seq<int>>
  requires 0 <= rows && 0 <= cols && rows == |a|
  ensures |BuildRowsFromA(a, rows, cols)| == rows
  ensures forall i :: 0 <= i < rows ==> |BuildRowsFromA(a, rows, cols)[i]| == cols
  ensures forall i, j :: 0 <= i < rows && 0 <= j < cols ==> BuildRowsFromA(a, rows, cols)[i][j] == a[i]
{
  BuildRowsFromA_Upto(a, cols, rows)
}

/* helper modified by LLM (iteration 2): build columns recursively to avoid comprehensions */
function BuildColsFromA_Upto(a: seq<int>, cols: int, k: int): seq<seq<int>>
  requires 0 <= k && cols == |a|
  ensures |BuildColsFromA_Upto(a, cols, k)| == k
  ensures forall i :: 0 <= i < k ==> |BuildColsFromA_Upto(a, cols, k)[i]| == cols
  ensures forall i, j :: 0 <= i < k && 0 <= j < cols ==> BuildColsFromA_Upto(a, cols, k)[i][j] == a[j]
  decreases k
{
  if k == 0 then []
  else BuildColsFromA_Upto(a, cols, k - 1) + [a]
}

/* helper modified by LLM (iteration 2): wrapper preserving original signature */
function BuildColsFromA(a: seq<int>, rows: int, cols: int): seq<seq<int>>
  requires 0 <= rows && cols == |a|
  ensures |BuildColsFromA(a, rows, cols)| == rows
  ensures forall i :: 0 <= i < rows ==> |BuildColsFromA(a, rows, cols)[i]| == cols
  ensures forall i, j :: 0 <= i < rows && 0 <= j < cols ==> BuildColsFromA(a, rows, cols)[i][j] == a[j]
{
  BuildColsFromA_Upto(a, cols, rows)
}
// </vc-helpers>

// <vc-spec>
method Broadcast(a: seq<int>, shape: seq<int>) returns (ret: Matrix<int>)
    requires 
        |a| > 0 &&
        |shape| == 2 &&
        shape[0] > 0 &&
        shape[1] > 0 &&
        (shape[0] == |a| || shape[1] == |a|)
    ensures
        MatrixWf(ret) &&
        ret.rows == shape[0] &&
        ret.cols == shape[1] &&
        MatrixSize(ret) == shape[0] * shape[1] &&
        (forall i, j :: 0 <= i < shape[0] && 0 <= j < shape[1] ==> (
            if shape[0] == |a| then
                MatrixIndex(ret, i, j) == a[i]
            else
                MatrixIndex(ret, i, j) == a[j]
        ))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): construct broadcasted matrix using recursive helpers */
  var rows := shape[0];
  var cols := shape[1];
  var data: seq<seq<int>>;
  if rows == |a| {
    data := BuildRowsFromA(a, rows, cols);
  } else {
    data := BuildColsFromA(a, rows, cols);
  }
  ret := Matrix(data, rows, cols);
}
// </vc-code>
