predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
lemma positive_prefix_property(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires forall k :: 0 <= k < i ==> s[k] >= 0
  ensures positive(s[0..i])
{
}
// </vc-helpers>

// <vc-spec>
method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
// </vc-spec>
// <vc-code>
{
  i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant positive(v[0..i])
  {
    if v[i] < 0 {
      b := true;
      return;
    }
    i := i + 1;
  }
  b := false;
  i := 0;
}
// </vc-code>

