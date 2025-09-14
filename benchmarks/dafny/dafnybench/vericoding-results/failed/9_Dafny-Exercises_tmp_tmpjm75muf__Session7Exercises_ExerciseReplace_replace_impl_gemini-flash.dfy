

// <vc-helpers>

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
  var old_v_length := v.Length; // Capture v.Length before modification
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall k:: 0 <= k < i && old(v[k]) == x ==> v[k] == y
    invariant forall k:: 0 <= k < i && old(v[k]) != x ==> v[k] == old(v[k])
    invariant forall k:: i <= k < old_v_length ==> v[k] == old(v[k])
    invariant v.Length == old_v_length
  {
    if v[i] == x {
      v[i] := y;
    }
    i := i + 1;
  }
}
// </vc-code>

