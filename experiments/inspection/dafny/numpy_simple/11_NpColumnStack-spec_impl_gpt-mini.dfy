// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): safe accessor for input[i][j] */
function GetElem(input: seq<seq<int>>, i: int, j: int): int
  requires 0 <= i < |input| && 0 <= j < |input[i]|
{
  input[i][j]
}
// </vc-helpers>

// <vc-spec>
method ColumnStack(input: seq<seq<int>>, m: int, n: int) returns (result: seq<seq<int>>)
    requires 
        n > 0 &&
        |input| == n &&
        (forall i :: 0 <= i < n ==> |input[i]| == m)
    ensures
        |result| == m &&
        (forall j :: 0 <= j < m ==> |result[j]| == n) &&
        |result| * n == m * n &&
        (forall i, j :: 0 <= i < n && 0 <= j < m ==> 
            result[j][i] == input[i][j])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): build result by iterating columns and rows, assert m>=0 */
  var res: seq<seq<int>> := [];
  assert 0 < n;
  assert |input[0]| == m;
  assert 0 <= |input[0]|;
  assert m >= 0;

  var j := 0;
  while j < m
    invariant 0 <= j <= m
    invariant |res| == j
    invariant (forall jj :: 0 <= jj < j ==> |res[jj]| == n && (forall ii :: 0 <= ii < n ==> res[jj][ii] == input[ii][jj]))
  {
    var col: seq<int> := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |col| == i
      invariant (forall ii :: 0 <= ii < i ==> col[ii] == input[ii][j])
    {
      col := col + [input[i][j]];
      i := i + 1;
    }
    res := res + [col];
    j := j + 1;
  }
  result := res;
}
// </vc-code>
