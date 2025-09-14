/**
  Inverts an array of ints.
 */

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n - i
    invariant 0 <= i
    invariant a.Length == n
    invariant i <= n - i + 1
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[n - 1 - j])
    invariant forall j :: 0 <= j < i ==> a[n - 1 - j] == old(a[j])
    invariant forall j :: i <= j < n - i ==> a[j] == old(a[j])
    decreases n + 1 - 2 * i
  {
    assert i < n;
    assert i <= n - i - 1;
    assert i <= n - 1;
    assert 0 <= n - 1 - i < n;

    var t := a[i];
    a[i] := a[n - 1 - i];
    a[n - 1 - i] := t;

    i := i + 1;
  }
}
// </vc-code>

