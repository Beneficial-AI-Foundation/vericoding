

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
// </vc-spec>
// <vc-code>
{
  ghost var oldV := v[..];
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant v.Length == |oldV|
    invariant forall k :: 0 <= k < i ==> (if oldV[k] == x then v[k] == y else v[k] == oldV[k])
    invariant forall k :: i <= k < v.Length ==> v[k] == oldV[k]
    decreases v.Length - i
  {
    if v[i] == x {
      v[i] := y;
    }
    i := i + 1;
  }
}
// </vc-code>

