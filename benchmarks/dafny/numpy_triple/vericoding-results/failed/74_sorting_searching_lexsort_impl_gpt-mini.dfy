// <vc-preamble>
// Perform an indirect stable sort using a sequence of keys
// Returns indices that lexicographically sort the input keys
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lexicographic comparator with stable tie-break */
function LexLess(keys: seq<seq<real>>, a: nat, b: nat): bool
  requires |keys| > 0
  requires forall k :: 0 <= k < |keys| ==> a < |keys[k]| && b < |keys[k]|
{
  (exists keyIdx :: 0 <= keyIdx < |keys| &&
     (forall l :: keyIdx < l && l < |keys| ==> keys[l][a] == keys[l][b]) &&
     keys[keyIdx][a] < keys[keyIdx][b])
  || ((forall l :: 0 <= l < |keys| ==> keys[l][a] == keys[l][b]) && a < b)
}

/* helper modified by LLM (iteration 5): totality lemma for LexLess using backward scan to find deciding key index */
lemma LexLess_total(keys: seq<seq<real>>, a: nat, b: nat)
  requires |keys| > 0
  requires forall k :: 0 <= k < |keys| ==> a < |keys[k]| && b < |keys[k]|
  requires a != b
  ensures LexLess(keys, a, b) || LexLess(keys, b, a)
{
  if forall l :: 0 <= l < |keys| ==> keys[l][a] == keys[l][b] {
    if a < b {
      assert LexLess(keys, a, b);
    } else {
      assert LexLess(keys, b, a);
    }
    return;
  }

  var keyIdx := |keys| - 1;
  while keyIdx > 0 && keys[keyIdx][a] == keys[keyIdx][b]
    decreases keyIdx
    invariant 0 <= keyIdx && keyIdx < |keys|
    invariant forall m :: keyIdx < m && m < |keys| ==> keys[m][a] == keys[m][b]
  {
    keyIdx := keyIdx - 1;
  }

  assert 0 <= keyIdx && keyIdx < |keys|;
  assert keys[keyIdx][a] != keys[keyIdx][b];
  if keys[keyIdx][a] < keys[keyIdx][b] {
    assert (exists keyIdx0 :: 0 <= keyIdx0 < |keys| && (forall l :: keyIdx0 < l && l < |keys| ==> keys[l][a] == keys[l][b]) && keys[keyIdx0][a] < keys[keyIdx0][b]);
    assert LexLess(keys, a, b);
  } else {
    assert LexLess(keys, b, a);
  }
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
/* code modified by LLM (iteration 5): stable insertion sort using LexLess and permutation invariants */
{
  var n := |keys[0]|;
  if n == 0 {
    indices := [];
    return;
  }
  indices := [0];
  var i := 1;
  while i < n
    decreases n - i
    invariant 0 <= i && i <= n
    invariant |indices| == i
    invariant forall k :: 0 <= k < i ==> 0 <= indices[k] < n
    invariant forall k :: 0 <= k < i ==> indices[k] < i
    invariant forall p, q :: 0 <= p < q < i ==> indices[p] != indices[q]
    invariant forall x :: 0 <= x < i ==> exists j :: 0 <= j < i && indices[j] == x
    invariant forall p, q :: 0 <= p < q < i ==> LexLess(keys, indices[p], indices[q])
  {
    var pos := 0;
    while pos < i
      decreases i - pos
      invariant 0 <= pos && pos <= i
      invariant forall k :: 0 <= k < pos ==> !LexLess(keys, i, indices[k])
    {
      if !LexLess(keys, i, indices[pos]) {
        pos := pos + 1;
      } else {
        break;
      }
    }

    var k := 0;
    while k < pos
      decreases pos - k
      invariant 0 <= k && k <= pos
      invariant forall t :: 0 <= t < k ==> indices[t] != i
    {
      assert indices[k] < i;
      assert indices[k] != i;
      LexLess_total(keys, indices[k], i);
      k := k + 1;
    }

    k := pos;
    while k < i
      decreases i - k
      invariant 0 <= k && k <= i
      invariant forall t :: k <= t < i ==> indices[t] != i
    {
      assert indices[k] < i;
      assert indices[k] != i;
      LexLess_total(keys, i, indices[k]);
      k := k + 1;
    }

    indices := indices[..pos] + [i] + indices[pos..];
    i := i + 1;
  }
}

// </vc-code>
