

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
                                            else a[i] == old(a[i])
ensures a.Length == old(a).Length
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var old_a_vals := a[0..n];

  for i := 0 to n - 1
    invariant 0 <= i <= n
    invariant a.Length == n
    invariant forall k :: 0 <= k < i ==> (if old_a_vals[k] < 0 then a[k] == 0 else a[k] == old_a_vals[k])
    invariant forall k :: i <= k < n ==> a[k] == old_a_vals[k]
    decreases n - i
  {
    if a[i] < 0 {
      a[i] := 0;
    }
  }
}
// </vc-code>

