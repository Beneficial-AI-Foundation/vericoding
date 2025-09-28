// <vc-preamble>
// Method that creates a triangular matrix with ones at and below the k-th diagonal
// </vc-preamble>

// <vc-helpers>

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
  result := [];
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant |result| == i
    invariant forall r :: 0 <= r < i ==> |result[r]| == M
    invariant forall r, c :: 0 <= r < i && 0 <= c < M ==> 
      result[r][c] == (if c <= r + k then 1.0 else 0.0)
  {
    var row := [];
    var j := 0;
    while j < M
      invariant 0 <= j <= M
      invariant |row| == j
      invariant forall c :: 0 <= c < j ==> 
        row[c] == (if c <= i + k then 1.0 else 0.0)
    {
      if j <= i + k {
        row := row + [1.0];
      } else {
        row := row + [0.0];
      }
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
}
// </vc-code>
