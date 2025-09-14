

// <vc-helpers>
ghost lemma SeqSnapshotPreservesLength(a: array<int>, s: seq<int>)
  requires s == a[..]
  ensures s.Length == a.Length
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
  ghost var oldv: seq<int> := v[..];
  var i := 0;
  while i < v.Length
    invariant 0 <= i && i <= v.Length
    invariant forall k :: 0 <= k && k < i && oldv[k] == x ==> v[k] == y
    invariant forall k :: 0 <= k && k < i && oldv[k] != x ==> v[k] == oldv[k]
    invariant forall k :: i <= k && k < v.Length ==> v[k] == oldv[k]
    decreases v.Length - i
  {
    if oldv[i] == x {
      v[i] := y;
    }
    assert oldv[i] == x ==> v[i] == y;
    assert oldv[i] != x ==> v[i] == oldv[i];
    i := i + 1;
  }
  // Help the verifier relate the snapshot sequence to the original array length
  SeqSnapshotPreservesLength(v, oldv);
}
// </vc-code>

