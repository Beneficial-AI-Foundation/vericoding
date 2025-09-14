predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  b := positive(v[0..v.Length]);
}
// </vc-code>

