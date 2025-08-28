predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
// Helper lemma to assist in proving properties if needed
lemma PositiveSeqLemma(s: seq<int>)
  ensures positive(s) == forall u :: 0 <= u < |s| ==> s[u] >= 0
{
  // This is just the definition of positive, so no further proof needed
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
// </vc-spec>
// </vc-spec>

// <vc-code>
method mpositiveImpl(v: array<int>) returns (b: bool)
  ensures b == positive(v[0..v.Length])
{
  b := true;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant b == forall u :: 0 <= u < i ==> v[u] >= 0
  {
    if v[i] < 0 {
      b := false;
      break;
    }
    i := i + 1;
  }
  // After the loop, if b is still true, all elements are non-negative
  if b {
    assert forall u :: 0 <= u < v.Length ==> v[u] >= 0;
  }
}
// </vc-code>
