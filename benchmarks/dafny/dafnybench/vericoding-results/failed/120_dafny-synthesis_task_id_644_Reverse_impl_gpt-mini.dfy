

// <vc-helpers>
// no helpers required
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>)
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n/2
    invariant 0 <= i <= n/2
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[n-1-k])
    invariant forall k :: 0 <= k < i ==> a[n-1-k] == old(a[k])
    invariant forall k :: i <= k <= n-1-i ==> a[k] == old(a[k])
    decreases n - 2*i
  {
    var tmp := a[i];
    a[i] := a[n-1-i];
    a[n-1-i] := tmp;
    i := i + 1;
  }
}
// </vc-code>

