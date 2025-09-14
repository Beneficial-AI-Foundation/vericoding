

// <vc-helpers>
lemma ReplaceLemma(v: array<int>, x: int, y: int, k: int)
  requires 0 <= k < v.Length
  ensures v[k] == old(v)[k] || v[k] == y
{
}

lemma AllElementsPreserved(v: array<int>, x: int, y: int, k: int)
  requires 0 <= k < v.Length
  requires old(v)[k] != x
  ensures v[k] == old(v)[k]
{
}

lemma AllElementsReplaced(v: array<int>, x: int, y: int, k: int)
  requires 0 <= k < v.Length
  requires old(v)[k] == x
  ensures v[k] == y
{
}
// </vc-helpers>

// <vc-spec>
method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  ghost var old_v := v[..];
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall k::0<=k<i && old_v[k]==x ==> v[k]==y
    invariant forall k::0<=k<i && old_v[k]!=x ==> v[k]==old_v[k]
    invariant forall k::i<=k<v.Length ==> v[k]==old_v[k]
  {
    if v[i] == x {
      v[i] := y;
    }
    i := i + 1;
  }
}
// </vc-code>

