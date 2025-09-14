

// <vc-helpers>
method Reverse(a: array<int>)
  modifies a
  ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-helpers>

// <vc-spec>
method Reverse(a: array<int>)
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[a.Length - 1 - j])
    invariant forall j :: a.Length - i <= j < a.Length ==> a[j] == old(a[a.Length - 1 - j])
    invariant forall k :: i <= k <= a.Length - 1 - i ==> a[k] == old(a[k])
  {
    var temp := a[i];
    a[i] := a[a.Length - 1 - i];
    a[a.Length - 1 - i] := temp;
    i := i + 1;
  }
}
// </vc-code>

