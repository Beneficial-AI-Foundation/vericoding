// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: a.Length - i <= k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: i <= k < a.Length - i ==> a[k] == old(a[k])
  {
    var temp := a[i];
    a[i] := a[a.Length - 1 - i];
    a[a.Length - 1 - i] := temp;
    i := i + 1;
  }
}
// </vc-code>
