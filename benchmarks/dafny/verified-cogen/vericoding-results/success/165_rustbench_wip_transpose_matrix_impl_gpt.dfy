// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): build a row of the transpose via recursion over the matrix rows */
function BuildRowUpTo(matrix: seq<seq<int>>, i: int, j: int): seq<int>
  requires |matrix| > 0
  requires forall r :: 0 <= r < |matrix| ==> |matrix[r]| == |matrix[0]|
  requires forall r :: 0 <= r < |matrix| ==> |matrix[r]| == |matrix|
  requires 0 <= i < |matrix[0]|
  requires 0 <= j <= |matrix|
  ensures |BuildRowUpTo(matrix, i, j)| == j
  ensures forall k :: 0 <= k < j ==> BuildRowUpTo(matrix, i, j)[k] == matrix[k][i]
  decreases j
{
  if j == 0 then
    []
  else
    BuildRowUpTo(matrix, i, j - 1) + [matrix[j - 1][i]]
}

/* helper modified by LLM (iteration 3): build the first i columns of the transpose */
function BuildTransposeUpTo(matrix: seq<seq<int>>, i: int): seq<seq<int>>
  requires |matrix| > 0
  requires forall r :: 0 <= r < |matrix| ==> |matrix[r]| == |matrix[0]|
  requires forall r :: 0 <= r < |matrix| ==> |matrix[r]| == |matrix|
  requires 0 <= i <= |matrix[0]|
  ensures |BuildTransposeUpTo(matrix, i)| == i
  ensures forall c :: 0 <= c < i ==> |BuildTransposeUpTo(matrix, i)[c]| == |matrix|
  ensures forall c, r :: 0 <= c < i && 0 <= r < |matrix| ==> BuildTransposeUpTo(matrix, i)[c][r] == matrix[r][c]
  decreases i
{
  if i == 0 then
    []
  else
    BuildTransposeUpTo(matrix, i - 1) + [BuildRowUpTo(matrix, i - 1, |matrix|)]
}

/* helper modified by LLM (iteration 3): expose final transpose builder using BuildTransposeUpTo */
function BuildTranspose(matrix: seq<seq<int>>): seq<seq<int>>
  requires |matrix| > 0
  requires forall r :: 0 <= r < |matrix| ==> |matrix[r]| == |matrix[0]|
  requires forall r :: 0 <= r < |matrix| ==> |matrix[r]| == |matrix|
  ensures |BuildTranspose(matrix)| == |matrix[0]|
  ensures forall c :: 0 <= c < |BuildTranspose(matrix)| ==> |BuildTranspose(matrix)[c]| == |matrix|
  ensures forall c, r :: 0 <= c < |BuildTranspose(matrix)| && 0 <= r < |BuildTranspose(matrix)[c]| ==> BuildTranspose(matrix)[c][r] == matrix[r][c]
{
  BuildTransposeUpTo(matrix, |matrix[0]|)
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
  /* code modified by LLM (iteration 3): construct the transpose using verified helper */
  result := BuildTranspose(matrix);
}
// </vc-code>
