predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

// <vc-helpers>
lemma PositivePrefix(v: array<int>, i: int)
  requires 0 <= i < v.Length
  requires positive(v[0..i])
  ensures forall k :: 0 <= k < i ==> v[k] >= 0
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
// </vc-spec>
// </vc-spec>

// <vc-code>
method FirstNegative(v: array<int>) returns (b: bool, i: int)
  ensures b <==> exists k :: 0 <= k < v.Length && v[k] < 0
  ensures b ==> 0 <= i < v.Length && v[i] < 0 && positive(v[0..i])
{
  b := false;
  i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant !b ==> positive(v[0..i])
    invariant b ==> 0 <= i < v.Length && v[i] < 0 && positive(v[0..i])
    invariant b <==> exists k :: 0 <= k < i && v[k] < 0
  {
    if v[i] < 0 {
      b := true;
      return;
    }
    i := i + 1;
  }
  return;
}
// </vc-code>
