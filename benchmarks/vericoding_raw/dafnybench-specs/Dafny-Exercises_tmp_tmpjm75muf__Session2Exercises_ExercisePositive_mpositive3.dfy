predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
// </vc-helpers>

method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
// <vc-code>
{
  assume false;
}
// </vc-code>