// RUN: /compile:0 /nologo

//IMPL CardinalitySubsetLt
method CardinalitySubsetLt<T>(A: set<T>, B: set<T>)
  requires A < B
  ensures |A| < |B|
{
  /* code modified by LLM (iteration 4): Use proper subset definition with clearer cardinality reasoning */
  // A < B means A is a proper subset of B (A ⊆ B and A ≠ B)
  assert A <= B;  // A is subset of B
  assert A != B;  // A is not equal to B
  
  /* code modified by LLM (iteration 4): Explicit cardinality reasoning using subset properties */
  // Since A ⊆ B, we have |A| ≤ |B|
  // Since A ≠ B and A ⊆ B, we must have |A| < |B|
  if |A| >= |B| {
    // This would contradict A < B
    assert |A| <= |B|; // from A ⊆ B
    assert |A| == |B|; // from our assumption and the above
    assert A == B;     // sets with same elements and same cardinality are equal when one is subset of other
    assert false;      // contradiction with A ≠ B
  }
  assert |A| < |B|;
}

//IMPL strategy
method strategy<T>(P: set<T>, Special: T) returns (count: int)
  requires |P| > 1 && Special in P
  ensures count == |P| - 1
{
  /* code modified by LLM (iteration 4): Calculate cardinality with explicit set operations */
  var remaining := P - {Special};
  count := |remaining|;
  
  /* code modified by LLM (iteration 4): Detailed cardinality assertions for verification */
  assert Special in P;
  assert Special !in remaining;
  assert remaining == P - {Special};
  assert P == remaining + {Special};
  assert remaining * {Special} == {};  // disjoint sets
  assert |P| == |remaining| + |{Special}|;  // cardinality of disjoint union
  assert |{Special}| == 1;
  assert |P| == |remaining| + 1;
  assert |remaining| == |P| - 1;
  assert count == |P| - 1;
}