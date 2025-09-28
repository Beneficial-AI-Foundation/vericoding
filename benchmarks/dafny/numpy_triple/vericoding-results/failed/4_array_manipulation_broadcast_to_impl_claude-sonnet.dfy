// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper lemma to prove value preservation postcondition */
lemma ValuePreservationLemma(v: seq<real>, result: seq<seq<real>>, m: nat)
  requires |result| == m
  requires forall i :: 0 <= i < m ==> result[i] == v
  requires |v| > 0
  ensures forall i, j :: 0 <= i < m && 0 <= j < |v| ==> exists k :: 0 <= k < |v| && result[i][j] == v[k] && k == j
{
  forall i, j | 0 <= i < m && 0 <= j < |v|
    ensures exists k :: 0 <= k < |v| && result[i][j] == v[k] && k == j
  {
    assert result[i] == v;
    assert result[i][j] == v[j];
    assert 0 <= j < |v|;
    assert result[i][j] == v[j] && j == j;
  }
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
  /* code modified by LLM (iteration 5): added call to helper lemma to prove value preservation */
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == |v|
    invariant forall k :: 0 <= k < i ==> result[k] == v
    invariant forall k1, k2 :: 0 <= k1 < i && 0 <= k2 < i ==> result[k1] == result[k2]
    invariant forall k, j :: 0 <= k < i && 0 <= j < |v| ==> result[k][j] == v[j]
    invariant forall k, j :: 0 <= k < i && 0 <= j < |v| ==> exists x :: 0 <= x < |v| && result[k][j] == v[x] && x == j
  {
    result := result + [v];
    i := i + 1;
  }
  
  ValuePreservationLemma(v, result, m);
}
// </vc-code>
