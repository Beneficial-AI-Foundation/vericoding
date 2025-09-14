predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
// Empty helpers section as no updates are needed
// </vc-helpers>

// <vc-spec>
method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  for i := 0 to v.Length
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[j] >= 0
  {
    if v[i] < 0 { return false; }
  }
  return true;
}
// </vc-code>

