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
  b := true;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant b == positive(v[0..i])
  {
    if v[i] < 0 {
      b := false;
    }
    i := i + 1;
  }
  assert v[0..v.Length] == v[..];
}
// </vc-code>

