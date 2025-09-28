// <vc-preamble>
// Method that creates a triangular matrix with ones at and below the k-th diagonal
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): define TriEntry function */
function TriEntry(i: int, j: int, k: int): real
{
  if j <= i + k then 1.0 else 0.0
}

/* helper modified by LLM (iteration 3): recursive function to build a row */
function Row(i: int, M: nat, k: int): seq<real>
  ensures |Row(i, M, k)| == M
  ensures forall j :: 0 <= j < M ==> Row(i, M, k)[j] == TriEntry(i, j, k)
  decreases M
{
  if M == 0 then []
  else Row(i, M - 1, k) + [TriEntry(i, M - 1, k)]
}

/* helper modified by LLM (iteration 3): recursive function to build the matrix */
function Matrix(N: nat, M: nat, k: int): seq<seq<real>>
  ensures |Matrix(N, M, k)| == N
  ensures forall i :: 0 <= i < N ==> |Matrix(N, M, k)[i]| == M
  ensures forall i, j :: 0 <= i < N && 0 <= j < M ==> Matrix(N, M, k)[i][j] == TriEntry(i, j, k)
  decreases N
{
  if N == 0 then []
  else Matrix(N - 1, M, k) + [Row(N - 1, M, k)]
}
// </vc-helpers>

// <vc-spec>
method tri(N: nat, M: nat, k: int) returns (result: seq<seq<real>>)
  // The result has exactly N rows
  ensures |result| == N
  // Each row has exactly M columns
  ensures forall i :: 0 <= i < N ==> |result[i]| == M
  // Each element is 1.0 if column index <= row index + k, otherwise 0.0
  ensures forall i, j :: 0 <= i < N && 0 <= j < M ==> 
    result[i][j] == (if j <= i + k then 1.0 else 0.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): construct matrix via recursive helper Matrix */
  result := Matrix(N, M, k);
}
// </vc-code>
