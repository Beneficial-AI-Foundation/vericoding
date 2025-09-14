// <vc-preamble>
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}
// </vc-preamble>

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
    invariant b <==> positive(v[0..i])
  {
    b := b && v[i] >= 0;
    i := i + 1;
  }
}
// </vc-code>
