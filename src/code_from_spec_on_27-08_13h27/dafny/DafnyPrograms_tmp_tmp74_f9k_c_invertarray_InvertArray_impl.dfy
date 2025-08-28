/**
  Inverts an array of ints.
 */

// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
// </vc-spec>
// </vc-spec>

// <vc-code>
method ArrayInversion(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
{
  var i := 0;
  var n := a.Length;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant forall k | 0 <= k < i :: a[k] == old(a[n-1-k])
    invariant forall k | 0 <= k < i :: a[n-1-k] == old(a[k])
    invariant forall k | i <= k < n - i :: a[k] == old(a[k])
  {
    var temp := a[i];
    a[i] := a[n-1-i];
    a[n-1-i] := temp;
    i := i + 1;
  }
}
// </vc-code>
