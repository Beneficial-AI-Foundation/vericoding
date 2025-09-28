// <vc-preamble>
// Method to find indices of non-zero elements in a sequence
// </vc-preamble>

// <vc-helpers>
predicate StrictlyIncreasing(s: seq<nat>)
  decreases s
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

lemma AppendPreservesStrictlyIncreasing(s: seq<nat>, x: nat)
  requires StrictlyIncreasing(s)
  requires forall k :: 0 <= k < |s| ==> s[k] < x
  ensures StrictlyIncreasing(s + [x])
{
  forall i, j | 0 <= i < j < |s| + 1
    ensures (s + [x])[i] < (s + [x])[j]
  {
    if j < |s| {
      assert (s + [x])[i] == s[i];
      assert (s + [x])[j] == s[j];
      assert s[i] < s[j];
    } else {
      assert j == |s|;
      assert i < |s|;
      assert (s + [x])[i] == s[i];
      assert (s + [x])[j] == x;
      assert s[i] < x;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method numpy_argwhere(a: seq<real>) returns (indices: seq<nat>)
  // No preconditions - accepts any sequence
  requires true
  // All returned indices must be valid positions in the input sequence
  ensures forall i :: 0 <= i < |indices| ==> indices[i] < |a|
  // All returned indices correspond to non-zero elements in the input
  ensures forall i :: 0 <= i < |indices| ==> a[indices[i]] != 0.0
  // All non-zero elements in the input have their indices in the result
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> j in indices
  // The result contains no duplicate indices
  ensures forall i, j :: 0 <= i < j < |indices| ==> indices[i] != indices[j]
  // The indices are in ascending order (ordered by their position in original vector)
  ensures forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
// </vc-spec>
// <vc-code>
{
  var acc: seq<nat> := [];
  var i: nat := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < |acc| ==> acc[k] < i
    invariant forall k :: 0 <= k < |acc| ==> acc[k] < |a|
    invariant forall k :: 0 <= k < |acc| ==> a[acc[k]] != 0.0
    invariant forall j :: 0 <= j < i && a[j] != 0.0 ==> j in acc
    invariant forall p, q :: 0 <= p < q < |acc| ==> acc[p] < acc[q]
    decreases |a| - i
  {
    if a[i] != 0.0 {
      acc := acc + [i];
    }
    i := i + 1;
  }
  indices := acc;
}
// </vc-code>
