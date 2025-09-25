// <vc-preamble>
// Perform an indirect stable sort using a sequence of keys
// Returns indices that lexicographically sort the input keys
// </vc-preamble>

// <vc-helpers>
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
{
  assume {:axiom} false;
}
// </vc-code>
