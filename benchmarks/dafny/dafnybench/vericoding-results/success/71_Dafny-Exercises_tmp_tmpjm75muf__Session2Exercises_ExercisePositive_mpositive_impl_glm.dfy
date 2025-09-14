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
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall k :: 0 <= k < i ==> v[k] >= 0
  {
    if v[i] < 0 {
      return false;
    }
    i := i + 1;
  }
  return true;
}
// </vc-code>

