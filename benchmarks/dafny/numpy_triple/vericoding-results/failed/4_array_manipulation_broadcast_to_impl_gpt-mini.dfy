// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove slice length equals array length */
lemma ArraySliceLength<T>(a: array<T>) ensures |a[..]| == a.Length {
  assert |a[..]| == a.Length;
}

/* helper modified by LLM (iteration 5): index equality from equal sequences */
lemma SeqEqIndex<T>(s1: seq<T>, s2: seq<T>, j: int)
  requires s1 == s2
  requires 0 <= j < |s1|
  ensures s1[j] == s2[j]
{
  assert s1[j] == s2[j];
}

/* helper modified by LLM (iteration 5): prove existential k==j for all entries when each row equals v */
lemma ForAllExistK(v: seq<real>, m: int, result: seq<seq<real>>)
  requires |v| > 0
  requires |result| == m
  requires forall i :: 0 <= i < m ==> result[i] == v
  ensures forall i, j :: 0 <= i < m && 0 <= j < |v| ==> exists k :: 0 <= k < |v| && result[i][j] == v[k] && k == j
{
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant forall ii :: 0 <= ii < i ==> forall j :: 0 <= j < |v| ==> (exists k :: 0 <= k < |v| && result[ii][j] == v[k] && k == j)
    decreases m - i
  {
    var j := 0;
    while j < |v|
      invariant 0 <= j <= |v|
      invariant forall jj :: 0 <= jj < j ==> (exists k :: 0 <= k < |v| && result[i][jj] == v[k] && k == jj)
      decreases |v| - j
    {
      var k := j;
      assert 0 <= k < |v|;
      assert result[i][j] == v[j];
      assert result[i][j] == v[k];
      assert k == j;
      assert exists kk :: 0 <= kk < |v| && result[i][j] == v[kk] && kk == j;
      j := j + 1;
    }
    i := i + 1;
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
  /* code modified by LLM (iteration 5): construct m rows by assigning v to each row and call helper to prove existential */
  var A := new seq<real>[m];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant A.Length == m
    invariant forall k :: 0 <= k < i ==> A[k] == v
    decreases m - i
  {
    A[i] := v;
    i := i + 1;
  }
  assert forall k :: 0 <= k < m ==> A[k] == v;
  result := A[..];
  assert |result| == m;
  assert forall ii :: 0 <= ii < m ==> result[ii] == v;
  ForAllExistK(v, m, result);
}

// </vc-code>
