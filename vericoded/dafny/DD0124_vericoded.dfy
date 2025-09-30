predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
// </vc-spec>
// <vc-code>
{
  var j := 0;
  while j < v.Length && v[j] >= 0
    decreases v.Length - j
    invariant 0 <= j <= v.Length
    invariant forall k :: 0 <= k < j ==> v[k] >= 0
  {
    j := j + 1;
  }
  if j < v.Length {
    b := true;
    i := j;
    assert v[i] < 0;
    assert positive(v[0..i]);
  } else {
    b := false;
    i := 0;
  }
}
// </vc-code>

