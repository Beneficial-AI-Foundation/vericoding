// <vc-preamble>
// </vc-preamble>

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
  /* code modified by LLM (iteration 5): fixed compilation error by using |v_old| for sequence length instead of v_old.Length */
  ghost var v_old := v[..];
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant v.Length == |v_old|
    invariant forall k :: 0 <= k < i && v_old[k] == x ==> v[k] == y
    invariant forall k :: 0 <= k < i && v_old[k] != x ==> v[k] == v_old[k]
    invariant forall k :: i <= k < v.Length ==> v[k] == v_old[k]
    modifies v
  {
    if v[i] == x {
      v[i] := y;
    }
    i := i + 1;
  }
}
// </vc-code>
