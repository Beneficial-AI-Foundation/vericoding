// <vc-preamble>
// Perform an indirect stable sort using a sequence of keys
// Returns indices that lexicographically sort the input keys
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed syntax by converting to expression-based if-else chain to resolve compilation error */
ghost function IsLessOrEqual(keys: seq<seq<real>>, p: nat, q: nat, keyIdx: nat): (res: bool)
  decreases |keys| - keyIdx
{
  if keyIdx == |keys| then true
  else if keys[keyIdx][p] < keys[keyIdx][q] then true
  else if keys[keyIdx][p] > keys[keyIdx][q] then false
  else IsLessOrEqual(keys, p, q, keyIdx + 1)
}
// </vc-helpers>

// <vc-spec>
method LexSort(keys: seq<seq<real>>) returns (indices: seq<nat>)
  // Input validation: at least one key sequence
  requires |keys| > 0
  // All key sequences must have the same length
  requires forall i :: 0 <= i < |keys| ==> |keys[i]| == |keys[0]|
  // Let n be the common length of all key sequences
  ensures var n := |keys[0]|;
    // Output has correct length
    |indices| == n &&
    // Output is a permutation of 0..n-1
    (forall i :: 0 <= i < n ==> 0 <= indices[i] < n) &&
    (forall i {:trigger} :: 0 <= i < n ==> exists j :: 0 <= j < n && indices[j] == i) &&
    (forall i, j :: 0 <= i < j < n ==> indices[i] != indices[j]) &&
    // Lexicographic ordering: for any two positions in the sorted result
    (forall i, j {:trigger} :: 0 <= i < j < n ==>
      (// There exists a key index where ordering is determined
      exists keyIdx :: 0 <= keyIdx < |keys| &&
        // All keys with higher priority (later in sequence) are equal
        (forall l :: keyIdx < l < |keys| ==> 
          keys[l][indices[i]] == keys[l][indices[j]]) &&
        // The determining key satisfies the ordering
        keys[keyIdx][indices[i]] <= keys[keyIdx][indices[j]])) &&
    // Stability: equal elements preserve original relative order
    (forall i, j {:trigger} :: 0 <= i < j < n ==>
      (forall l :: 0 <= l < |keys| ==> keys[l][i] == keys[l][j]) ==>
      exists p, q :: 0 <= p < q < n && indices[p] == i && indices[q] == j)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Maintained insertion sort logic with existing invariants for permutation and ordering */
{
  var n := |keys[0]|;
  var indices: seq<nat> := seq(n, i => i);
  for (i := 1; i < n; i := i + 1)
  invariant 1 <= i <= n
  invariant |indices| == n
  invariant forall k :: 0 <= k < n ==> 0 <= indices[k] < n
  invariant forall k :: 0 <= k < n ==> exists l :: 0 <= l < n && indices[l] == k
  invariant forall k1, k2 :: 0 <= k1 < k2 < n ==> indices[k1] != indices[k2]
  invariant forall k1, k2 :: 0 <= k1 < k2 <= i ==> IsLessOrEqual(keys, indices[k1], indices[k2], 0)
  {
    var val := indices[i];
    var temp: seq<nat> := [];
    var k := 0;
    while (k < i && IsLessOrEqual(keys, indices[k], val, 0))
    invariant 0 <= k <= i
    invariant |temp| == k
    invariant forall j :: 0 <= j < k ==> temp[j] == indices[j]
    invariant forall j :: 0 <= j < k ==> !IsLessOrEqual(keys, val, indices[j], 0)
    {
      temp := temp + [indices[k]];
      k := k + 1;
    }
    indices := temp + [val] + indices[k .. i] + indices[i + 1 .. ];
  }
  return indices;
}
// </vc-code>
