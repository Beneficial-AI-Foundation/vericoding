// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
                                            else a[i] == old(a[i])
ensures a.Length == old(a).Length
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  for i := 0 to a.Length
  invariant 0 <= i <= a.Length
  invariant forall k :: 0 <= k < i ==> if old(a[k]) < 0 then a[k] == 0 else a[k] == old(a[k])
  invariant forall k :: i <= k < a.Length ==> a[k] == old(a[k])
  {
    if a[i] < 0 {
      a[i] := 0;
    }
  }
}
// </vc-code>
