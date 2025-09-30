// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): predicate for strictly increasing sequences of nat */
predicate StrictlyIncreasing(s: seq<nat>)
{
  forall i:int, j:int :: 0 <= i < j < |s| ==> s[i] < s[j]
}

/* helper modified by LLM (iteration 3): appending a larger element preserves StrictlyIncreasing */
lemma StrictlyIncreasingAppend(s: seq<nat>, x: int)
  requires StrictlyIncreasing(s)
  requires forall p:int :: 0 <= p < |s| ==> s[p] < x
  requires 0 <= x
  ensures StrictlyIncreasing(s + [x as nat])
{
  var t := s + [x as nat];
  forall p:int, q:int
    | 0 <= p < q < |t|
    ensures t[p] < t[q]
  {
    if q < |s| {
      assert 0 <= p < q < |s|;
      assert t[p] == s[p];
      assert t[q] == s[q];
      assert s[p] < s[q];
    } else {
      assert q == |s|;
      assert 0 <= p < |s|;
      assert t[p] == s[p];
      assert t[q] == x as nat;
      assert s[p] < x;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method nonzero(a: seq<real>) returns (indices: seq<nat>)
  // No preconditions - accepts any sequence
  requires true
  // Every returned index must be valid and correspond to a non-zero element
  ensures forall i :: i in indices ==> i < |a| && a[i] != 0.0
  // Every non-zero element must have its index in the result (completeness)
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> j in indices
  // The indices are returned in ascending order
  ensures forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
  // No duplicates in the result (implied by ascending order, but made explicit)
  ensures forall i, j :: 0 <= i < |indices| && 0 <= j < |indices| && i != j ==> indices[i] != indices[j]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): linear scan that collects indices of non-zero entries while maintaining strict order via lemma */
  var res: seq<nat> := [];
  var i: int := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: k in res ==> k < i && a[k] != 0.0
    invariant forall j :: 0 <= j < i && a[j] != 0.0 ==> j in res
    invariant StrictlyIncreasing(res)
    invariant forall p :: 0 <= p < |res| ==> res[p] < i
    invariant |res| == 0 || res[|res|-1] < i
  {
    if a[i] != 0.0 {
      StrictlyIncreasingAppend(res, i);
      res := res + [i as nat];
    }
    i := i + 1;
  }
  indices := res;
}
// </vc-code>
