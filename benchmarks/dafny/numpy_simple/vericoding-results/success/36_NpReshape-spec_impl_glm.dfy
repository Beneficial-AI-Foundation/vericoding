// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(mat: Matrix<T>): nat
{
    if |mat| == 0 then 0 else |mat| * |mat[0]|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Reshape(arr: seq<int>, shape: seq<nat>) returns (result: Matrix<int>)
    requires 
        |arr| > 0 &&
        |shape| == 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed if-statement syntax by removing 'then' */
  var rows := shape[0];
  var cols := shape[1];
  result := [];
  var k := 0;
  for i := 0 to rows
  {
    var row := [];
    for j := 0 to cols
    {
      if k < |arr| {
        row := row + [arr[k]];
      } else {
        row := row + [0];
      }
      k := k + 1;
    }
    result := result + [row];
  }
}
// </vc-code>
