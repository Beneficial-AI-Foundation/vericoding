// <vc-preamble>
// Method to find indices of all non-zero elements in a sequence
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): trivial lemma to satisfy helpers section */
lemma TrueHelper() ensures true {
}

// </vc-helpers>

// <vc-spec>
method FlatNonZero(a: seq<real>) returns (result: seq<nat>)
  // No preconditions - accepts any sequence of reals
  ensures |result| <= |a|
  // All indices in result are valid and point to non-zero elements
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] < |a| && a[result[i]] != 0.0
  // All non-zero elements have their indices in result
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> j in result
  // Result contains no duplicate indices
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // Result indices are sorted in ascending order
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implement loop collecting non-zero indices and maintain invariants including |res| <= i */
{
  var res: seq<nat> := [];
  var i: nat := 0;
  while i < |a|
    invariant 0 <= i && i <= |a|
    invariant |res| <= i
    invariant forall k :: 0 <= k < |res| ==> 0 <= res[k] < i && a[res[k]] != 0.0
    invariant forall j :: 0 <= j < i && a[j] != 0.0 ==> j in res
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] < res[q]
  {
    if a[i] != 0.0 {
      res := res + [i];
    }
    i := i + 1;
  }
  result := res;
}

// </vc-code>
