// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(mat: Matrix<T>): nat
{
    if |mat| == 0 then 0 else |mat| * |mat[0]|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): compute wrapped flat index */
function FlatIndex(cols: nat, row: nat, col: nat, arrLen: nat): nat
  requires arrLen > 0
{
  (row * cols + col) % arrLen
}

// </vc-helpers>

// <vc-spec>
method Reshape(arr: seq<int>, shape: seq<nat>) returns (result: Matrix<int>)
    requires 
        |arr| > 0 &&
        |shape| == 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build matrix row-major with wrapping */
  var rows := shape[0];
  var cols := shape[1];
  var arrLen := |arr|;
  var res: seq<seq<int>> := [];
  var r: nat := 0;
  while r < rows
    invariant 0 <= r <= rows
    invariant |res| == r
  {
    var c: nat := 0;
    var rowseq: seq<int> := [];
    while c < cols
      invariant 0 <= c <= cols
      invariant |rowseq| == c
    {
      var idx := (r * cols + c) % arrLen;
      assert 0 <= idx < arrLen;
      rowseq := rowseq + [arr[idx]];
      c := c + 1;
    }
    res := res + [rowseq];
    r := r + 1;
  }
  result := res;
}

// </vc-code>
