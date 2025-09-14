

// <vc-helpers>
// empty helpers section after fixing verification errors
// </vc-helpers>

// <vc-spec>
method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
// </vc-spec>
// <vc-code>
{
  ghost var old_v := old(v[..]);
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i && old_v[j] == x ==> v[j] == y
    invariant forall j :: 0 <= j < i && old_v[j] != x ==> v[j] == old_v[j]
  {
    if v[i] == x {
      v[i] := y;
    }
    i := i + 1;
  }
}
// </vc-code>

