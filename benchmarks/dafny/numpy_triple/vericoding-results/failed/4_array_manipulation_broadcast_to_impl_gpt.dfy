// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): helper to construct a constant sequence of length n with element x */
function ConstSeq<T>(n: nat, x: T): seq<T>
  decreases n
  ensures |ConstSeq(n, x)| == n
  ensures forall i :: 0 <= i < n ==> ConstSeq(n, x)[i] == x
{
  if n == 0 then [] else [x] + ConstSeq(n - 1, x)
}
// </vc-helpers>

// <vc-spec>
method BroadcastTo(v: seq<real>, m: nat) returns (result: seq<seq<real>>)
  requires |v| > 0  // Input vector must be non-empty
  requires m > 0    // Target number of rows must be positive
  ensures |result| == m  // Result has exactly m rows
  ensures forall i :: 0 <= i < m ==> |result[i]| == |v|  // Each row has same length as input
  // Primary property: each element (i,j) equals v[j]
  ensures forall i, j :: 0 <= i < m && 0 <= j < |v| ==> result[i][j] == v[j]
  // Row identity: each row is exactly the input vector  
  ensures forall i :: 0 <= i < m ==> result[i] == v
  // Column uniformity: each column contains a single repeated value
  ensures forall j, i1, i2 :: 0 <= j < |v| && 0 <= i1 < m && 0 <= i2 < m ==> result[i1][j] == result[i2][j]
  // Value preservation: no new values are introduced, each element comes from original vector
  ensures forall i, j :: 0 <= i < m && 0 <= j < |v| ==> exists k :: 0 <= k < |v| && result[i][j] == v[k] && k == j
  // Broadcast invariant: all rows are identical
  ensures forall i1, i2 :: 0 <= i1 < m && 0 <= i2 < m ==> result[i1] == result[i2]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build m rows each equal to v via ConstSeq */
  result := ConstSeq(m, v);
}
// </vc-code>
