// <vc-preamble>
// Perform an indirect stable sort using a sequence of keys
// Returns indices that lexicographically sort the input keys
// </vc-preamble>

// <vc-helpers>
predicate IsPermutation(indices: seq<nat>, n: nat)
{
  |indices| == n &&
  (forall i :: 0 <= i < n ==> 0 <= indices[i] < n) &&
  (forall i {:trigger indices[i]} :: 0 <= i < n ==> exists j :: 0 <= j < n && indices[j] == i) &&
  (forall i, j :: 0 <= i < j < n ==> indices[i] != indices[j])
}

function InitialSequence(n: nat): seq<nat>
  ensures |InitialSequence(n)| == n
  ensures forall i :: 0 <= i < n ==> InitialSequence(n)[i] == i
  ensures forall i :: 0 <= i < n ==> 0 <= InitialSequence(n)[i] < n
  ensures forall i {:trigger InitialSequence(n)[i]} :: 0 <= i < n ==> exists j :: 0 <= j < n && InitialSequence(n)[j] == i
{
  if n == 0 then [] else [n - 1] + InitialSequence(n - 1)
}

/* helper modified by LLM (iteration 5): simplified permutation lemma */
lemma InitialSequencePermutation(n: nat)
  ensures var s := InitialSequence(n);
    |s| == n &&
    (forall i :: 0 <= i < n ==> 0 <= s[i] < n) &&
    (forall i :: 0 <= i < n ==> exists j :: 0 <= j < n && s[j] == i) &&
    (forall i, j :: 0 <= i < j < n ==> s[i] != s[j])
{
  var s := InitialSequence(n);
  if n == 0 {
    return;
  }
  InitialSequencePermutation(n - 1);
  assert s[0] == n - 1;
}

/* helper modified by LLM (iteration 5): removed problematic swap lemma */
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
  /* code modified by LLM (iteration 5): simplified implementation without complex helpers */
  var n := |keys[0]|;
  if n == 0 {
    indices := [];
    return;
  }
  
  indices := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |indices| == i
    invariant forall k :: 0 <= k < i ==> indices[k] == k
  {
    indices := indices + [i];
    i := i + 1;
  }
  
  var keyIdx := |keys| - 1;
  while keyIdx >= 0
    invariant -1 <= keyIdx < |keys|
    invariant |indices| == n
    invariant forall i :: 0 <= i < n ==> 0 <= indices[i] < n
    invariant forall i :: 0 <= i < n ==> exists j :: 0 <= j < n && indices[j] == i
    invariant forall i, j :: 0 <= i < j < n ==> indices[i] != indices[j]
  {
    i := 0;
    while i < n - 1
      invariant 0 <= i <= n - 1
      invariant |indices| == n
      invariant forall k :: 0 <= k < n ==> 0 <= indices[k] < n
      invariant forall k :: 0 <= k < n ==> exists j :: 0 <= j < n && indices[j] == k
      invariant forall p, q :: 0 <= p < q < n ==> indices[p] != indices[q]
    {
      var j := i + 1;
      while j < n
        invariant i + 1 <= j <= n
        invariant |indices| == n
        invariant forall k :: 0 <= k < n ==> 0 <= indices[k] < n
        invariant forall k :: 0 <= k < n ==> exists l :: 0 <= l < n && indices[l] == k
        invariant forall p, q :: 0 <= p < q < n ==> indices[p] != indices[q]
      {
        if keys[keyIdx][indices[j]] < keys[keyIdx][indices[i]] ||
           (keys[keyIdx][indices[j]] == keys[keyIdx][indices[i]] && indices[j] < indices[i]) {
          var temp := indices[i];
          indices := indices[i := indices[j]][j := temp];
        }
        j := j + 1;
      }
      i := i + 1;
    }
    keyIdx := keyIdx - 1;
  }
}
// </vc-code>
