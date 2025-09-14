// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): isSquare predicate */
predicate IsSquare(matrix: seq<seq<int>>) { |matrix| > 0 && forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]| && |matrix[i]| == |matrix| }

/* helper modified by LLM (iteration 4): RowLen returns length of first row */
function RowLen(matrix: seq<seq<int>>): int requires |matrix| > 0 { |matrix[0]| }

/* helper modified by LLM (iteration 4): lemma proving row length equals n for square matrices */
lemma SquareRowLenEqualsN(matrix: seq<seq<int>>) requires IsSquare(matrix) ensures RowLen(matrix) == |matrix| {
  assert RowLen(matrix) == |matrix[0]|;
  assert |matrix[0]| == |matrix|;
}

// </vc-helpers>

// <vc-spec>
method Transpose(matrix: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |matrix| > 0
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
    requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
    ensures |result| == |matrix[0]|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |matrix|
    ensures forall i, j :: 0 <= i < |result| && 0 <= j < |result[i]| ==> result[i][j] == matrix[j][i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Build transpose using nested loops and sequence concatenation */
  var n := RowLen(matrix);
  var m := |matrix|;
  result := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == i
    invariant forall ii :: 0 <= ii < |result| ==> |result[ii]| == m
    invariant forall ii, jj :: 0 <= ii < |result| && 0 <= jj < |result[ii]| ==> result[ii][jj] == matrix[jj][ii]
  {
    var row := [];
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant |row| == j
      invariant forall jj :: 0 <= jj < |row| ==> row[jj] == matrix[jj][i]
    {
      row := row + [matrix[j][i]];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}

// </vc-code>
