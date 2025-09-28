// <vc-preamble>
// Perform an indirect stable sort using a sequence of keys
// Returns indices that lexicographically sort the input keys
// </vc-preamble>

// <vc-helpers>

  /* helper modified by LLM (iteration 5): Fix bounds checking and triggers */
  predicate IsPermutation(s: seq<nat>, n: int)
    requires 0 <= n
  {
    |s| == n &&
    (forall i :: 0 <= i < n ==> 0 <= s[i] < n) &&
    (forall i :: 0 <= i < n ==> exists j :: 0 <= j < n && s[j] == i)
  }

  /* helper modified by LLM (iteration 5): Add bounds checking and fix array access */
  predicate LexOrdered(keys: seq<seq<real>>, indices: seq<nat>, i: int, j: int)
    requires 0 <= i < j < |indices|
    requires |keys| > 0
    requires forall k :: 0 <= k < |keys| ==> |keys[k]| == |indices|
  {
    exists keyIdx :: 0 <= keyIdx < |keys| &&
      (forall l :: keyIdx < l < |keys| ==> 
        0 <= indices[i] < |keys[l]| && 0 <= indices[j] < |keys[l]| &&
        keys[l][indices[i]] == keys[l][indices[j]]) &&
      0 <= indices[i] < |keys[keyIdx]| && 0 <= indices[j] < |keys[keyIdx]| &&
      keys[keyIdx][indices[i]] <= keys[keyIdx][indices[j]]
  }

  /* helper modified by LLM (iteration 5): Add bounds checking for array access */
  predicate Stable(keys: seq<seq<real>>, indices: seq<nat>, n: int)
    requires |keys| > 0
    requires forall k :: 0 <= k < |keys| ==> |keys[k]| == n
  {
    forall i, j :: 
      (0 <= i < j < n) && 
      (forall l :: 0 <= l < |keys| ==> 0 <= i < |keys[l]| && 0 <= j < |keys[l]| && keys[l][i] == keys[l][j]) ==>
        exists p, q :: 0 <= p < q < n && indices[p] == i && indices[q] == j
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
{
  /* code modified by LLM (iteration 5): Fix bounds checking and indexing */
  var n := |keys[0]|;
  var result: seq<nat> := seq(n, i => i);
  
  if n <= 1 {
    indices := result;
    return;
  }
  
  var swapped := true;
  var count := 0;
  
  while swapped && count < n * |keys|
    invariant |result| == n
    invariant IsPermutation(result, n)
    decreases if swapped then n * |keys| - count else 0
  {
    swapped := false;
    
    for pass := 0 to n - 2
      invariant |result| == n
      invariant IsPermutation(result, n)
    {
      var shouldSwap := false;
      var comparingKey := 0;
      
      while comparingKey < |keys| && 
            comparingKey < |keys| && 0 <= result[pass] < |keys[comparingKey]| &&
            0 <= result[pass+1] < |keys[comparingKey]| &&
            keys[comparingKey][result[pass]] == keys[comparingKey][result[pass+1]]
        invariant 0 <= comparingKey <= |keys|
        invariant (forall l :: 0 <= l < comparingKey ==> 
                  0 <= result[pass] < |keys[l]| && 0 <= result[pass+1] < |keys[l]| &&
                  keys[l][result[pass]] == keys[l][result[pass+1]])
      {
        comparingKey := comparingKey + 1;
      }
      
      if comparingKey < |keys| && 
         0 <= result[pass] < |keys[comparingKey]| &&
         0 <= result[pass+1] < |keys[comparingKey]| &&
         keys[comparingKey][result[pass]] > keys[comparingKey][result[pass+1]] {
        shouldSwap := true;
      }
      
      if shouldSwap {
        result := result[0..pass] + [result[pass+1], result[pass]] + result[pass+2..];
        swapped := true;
      }
    }
    
    count := count + 1;
  }
  
  indices := result;
}
// </vc-code>
