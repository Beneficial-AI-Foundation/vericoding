// <vc-preamble>
// Method that creates a triangular matrix with ones at and below the k-th diagonal
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed lemma proofs since they are not needed and compilation failed */
function IsValidIndex(i: int, j: int, k: int): bool {
  j <= i + k
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
/* code modified by LLM (iteration 2): Fixed syntax error in sequence comprehension */
{
  result := seq(N, i => seq(M, j => (if j <= i + k then 1.0 else 0.0)));
}
// </vc-code>
