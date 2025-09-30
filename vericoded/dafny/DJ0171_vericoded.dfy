// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fixed BuildRowCorrect lemma to handle row >= |matrix| case properly */
function BuildRow(matrix: seq<seq<int>>, col: int, row: int): seq<int>
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires 0 <= col < |matrix[0]|
  requires 0 <= row <= |matrix|
  decreases |matrix| - row
{
  if row == |matrix| then []
  else [matrix[row][col]] + BuildRow(matrix, col, row + 1)
}

function BuildTranspose(matrix: seq<seq<int>>, col: int): seq<seq<int>>
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires 0 <= col <= |matrix[0]|
  decreases |matrix[0]| - col
{
  if col == |matrix[0]| then []
  else [BuildRow(matrix, col, 0)] + BuildTranspose(matrix, col + 1)
}

lemma BuildRowLength(matrix: seq<seq<int>>, col: int, row: int)
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires 0 <= col < |matrix[0]|
  requires 0 <= row <= |matrix|
  ensures |BuildRow(matrix, col, row)| == |matrix| - row
  decreases |matrix| - row
{
  if row == |matrix| {
  } else {
    BuildRowLength(matrix, col, row + 1);
  }
}

lemma BuildRowCorrect(matrix: seq<seq<int>>, col: int, row: int, k: int)
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires 0 <= col < |matrix[0]|
  requires 0 <= row <= |matrix|
  requires 0 <= k < |matrix| - row
  ensures row + k < |matrix|
  ensures |BuildRow(matrix, col, row)| > k
  ensures BuildRow(matrix, col, row)[k] == matrix[row + k][col]
  decreases |matrix| - row
{
  if row == |matrix| {
  } else if k == 0 {
  } else {
    BuildRowCorrect(matrix, col, row + 1, k - 1);
  }
}

lemma BuildTransposeCorrect(matrix: seq<seq<int>>, col: int)
  requires |matrix| > 0
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix[0]|
  requires forall i :: 0 <= i < |matrix| ==> |matrix[i]| == |matrix|
  requires 0 <= col <= |matrix[0]|
  ensures |BuildTranspose(matrix, col)| == |matrix[0]| - col
  ensures forall i :: 0 <= i < |BuildTranspose(matrix, col)| ==> |BuildTranspose(matrix, col)[i]| == |matrix|
  ensures forall i, j :: 0 <= i < |BuildTranspose(matrix, col)| && 0 <= j < |BuildTranspose(matrix, col)[i]| ==> BuildTranspose(matrix, col)[i][j] == matrix[j][col + i]
  decreases |matrix[0]| - col
{
  if col == |matrix[0]| {
  } else {
    BuildRowLength(matrix, col, 0);
    BuildTransposeCorrect(matrix, col + 1);
    forall i, j | 0 <= i < |BuildTranspose(matrix, col)| && 0 <= j < |BuildTranspose(matrix, col)[i]|
      ensures BuildTranspose(matrix, col)[i][j] == matrix[j][col + i]
    {
      if i == 0 {
        BuildRowCorrect(matrix, col, 0, j);
      } else {
        assert BuildTranspose(matrix, col)[i][j] == BuildTranspose(matrix, col + 1)[i - 1][j];
      }
    }
  }
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
/* code modified by LLM (iteration 2): Simple implementation calling BuildTranspose */
{
  result := BuildTranspose(matrix, 0);
  BuildTransposeCorrect(matrix, 0);
}
// </vc-code>
