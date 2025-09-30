// <vc-preamble>
type Matrix<T> = seq<seq<T>>

function MatrixSize<T>(m: Matrix<T>): nat
{
    (|m| * (if |m| > 0 then |m[0]| else 0)) as nat
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed TrilRow function to handle empty sequences correctly and adjust column index */
function TrilRow(row: seq<int>, rowIndex: int, k: int, colIndex: int): seq<int>
  decreases |row|
  ensures |TrilRow(row, rowIndex, k, colIndex)| == |row|
  ensures forall j :: 0 <= j < |row| ==>
    if (colIndex + j) - rowIndex > k then TrilRow(row, rowIndex, k, colIndex)[j] == 0
    else TrilRow(row, rowIndex, k, colIndex)[j] == row[j]
{
  if |row| == 0 then []
  else if colIndex - rowIndex > k then [0] + TrilRow(row[1..], rowIndex, k, colIndex + 1)
  else [row[0]] + TrilRow(row[1..], rowIndex, k, colIndex + 1)
}
// </vc-helpers>

// <vc-spec>
method Tril(arr: Matrix<int>, k: int) returns (ret: Matrix<int>)
    requires 
        |arr| > 0 &&
        |arr[0]| > 0 &&
        (forall i :: 0 <= i < |arr| ==> |arr[i]| == |arr[0]|) &&
        -((|arr| as int) - 1) < k && k < (|arr[0]| as int) - 1
    ensures
        MatrixSize(ret) == MatrixSize(arr) &&
        |ret| == |arr| &&
        (forall i :: 0 <= i < |ret| ==> |ret[i]| == |arr[0]|) &&
        forall i: int, j: int :: 
            0 <= i < |arr| && 0 <= j < |arr[0]| ==> 
                if j - i > k then ret[i][j] == 0 else ret[i][j] == arr[i][j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Use TrilRow helper function to build each row */
  var result: seq<seq<int>> := [];
  var i := 0;
  
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant |result| == i
    invariant forall m :: 0 <= m < i ==> |result[m]| == |arr[0]|
    invariant forall m: int, n: int :: 0 <= m < i && 0 <= n < |arr[0]| ==>
      if n - m > k then result[m][n] == 0 else result[m][n] == arr[m][n]
  {
    var newRow := TrilRow(arr[i], i, k, 0);
    result := result + [newRow];
    i := i + 1;
  }
  
  ret := result;
}
// </vc-code>
