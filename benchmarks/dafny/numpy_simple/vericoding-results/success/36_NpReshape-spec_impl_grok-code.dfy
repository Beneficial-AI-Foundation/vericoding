// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(mat: Matrix<T>): nat
{
    if |mat| == 0 then 0 else |mat| * |mat[0]|
}
// </vc-preamble>

// <vc-helpers>
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method Reshape(arr: seq<int>, shape: seq<nat>) returns (result: Matrix<int>)
    requires 
        |arr| > 0 &&
        |shape| == 2
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added guard for rows > 0 to fix lower bound error in loop */
{
  var rows := shape[0] as int;
  var cols := shape[1] as int;
  var res := [];
  if rows > 0 {
    for i := 0 to rows - 1
    {
      var start := i * cols;
      var endPosition := start + cols;
      var sliceEnd := if endPosition < |arr| then endPosition else |arr|;
      var rowSlice := if start < |arr| then arr[start..sliceEnd] else [];
      var paddingNeeded := cols - |rowSlice|;
      var counter := 0;
      while counter < paddingNeeded
      {
        rowSlice := rowSlice + [0];
        counter := counter + 1;
      }
      res := res + [rowSlice];
    }
  }
  result := res;
}
// </vc-code>
