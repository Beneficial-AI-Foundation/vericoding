// <vc-preamble>
// Perform an indirect stable sort using a sequence of keys
// Returns indices that lexicographically sort the input keys
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The loop condition `while k < keys.Length` was causing a compilation error. This was because `keys` is a sequence of sequences, and `keys.Length` should be `|keys|`. The `lexicographic_compare` function signature already specifies that `keys` is a `seq<seq<real>>`, so `|keys|` is the correct way to get the length. The loop condition is changed to use `|keys|` instead of `keys.Length`. */
function lexicographic_compare(keys: seq<seq<real>>, idx1: nat, idx2: nat): (ord: int) 
  requires |keys| > 0
  requires forall i :: 0 <= i < |keys| ==> |keys[i]| == |keys[0]|
  requires 0 <= idx1 < |keys[0]|
  requires 0 <= idx2 < |keys[0]|
{
  var k := 0;
  while k < |keys|
    invariant 0 <= k <= |keys|
    invariant forall l :: 0 <= l < k ==> keys[l][idx1] == keys[l][idx2]
  {
    if keys[k][idx1] < keys[k][idx2] then return -1;
    if keys[k][idx1] > keys[k][idx2] then return 1;
    k := k + 1;
  }
  return 0; // Equal
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
/* code modified by LLM (iteration 5): The compilation error in `lexicographic_compare` has been resolved by fixing the loop condition in the helper function. This code now uses the corrected helper. */
{
  var n := |keys[0]|;
  var indices_arr := new nat[n];
  for i := 0 to n - 1 do
    indices_arr[i] := i;

  // Using a bubble sort-like approach for stable sort
  for i := 0 to n - 2
    invariant 0 <= i < n - 1
    invariant |indices_arr| == n
  {
    for j := n - 1 to i + 1 by -1
      invariant i < j <= n
      invariant |indices_arr| == n
    {
      var compare_result := lexicographic_compare(keys, indices_arr[j - 1], indices_arr[j]);
      // For stability, if equal, maintain original relative order (smaller index comes first)
      if compare_result == 1 || (compare_result == 0 && indices_arr[j - 1] > indices_arr[j]) {
        var temp := indices_arr[j - 1];
        indices_arr[j - 1] := indices_arr[j];
        indices_arr[j] := temp;
      }
    }
  }

  indices := indices_arr;
}
// </vc-code>
