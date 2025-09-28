// <vc-preamble>
// Perform an indirect stable sort using a sequence of keys
// Returns indices that lexicographically sort the input keys
// </vc-preamble>

// <vc-helpers>
function FindFirstDiff(i: nat, j: nat, keys: seq<seq<real>>, start: nat): nat
  decreases |keys| - start
{
  if start >= |keys| then |keys|
  else if keys[start][i] != keys[start][j] then start
  else FindFirstDiff(i, j, keys, start+1)
}

function LexCompare(i: nat, j: nat, keys: seq<seq<real>>): int
{
  if i == j then 0
  else
    var firstDiff := FindFirstDiff(i, j, keys, 0);
    if firstDiff < |keys| then
      if keys[firstDiff][i] < keys[firstDiff][j] then -1
      else if keys[firstDiff][i] > keys[firstDiff][j] then 1
      else 0
    else
      if i < j then -1 else 1
}

/* helper modified by LLM (iteration 2): fixed function syntax */
function MergeSort(arr: seq<nat>, keys: seq<seq<real>>): seq<nat>
  decreases |arr|
{
  if |arr| <= 1 then arr
  else
    var mid := |arr| / 2;
    var left := MergeSort(arr[..mid], keys);
    var right := MergeSort(arr[mid..], keys);
    Merge(left, right, keys)
}

/* helper modified by LLM (iteration 2): fixed function syntax */
function Merge(left: seq<nat>, right: seq<nat>, keys: seq<seq<real>>): seq<nat>
  decreases |left| + |right|
{
  if |left| == 0 then right
  else if |right| == 0 then left
  else
    if LexCompare(left[0], right[0], keys) <= 0 then
      [left[0]] + Merge(left[1..], right, keys)
    else
      [right[0]] + Merge(left, right[1..], keys)
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
  /* code modified by LLM (iteration 2): unchanged */
  var n := |keys[0]|;
  var indices := seq(n, i => i);
  indices := MergeSort(indices, keys);
  return indices;
}
// </vc-code>
