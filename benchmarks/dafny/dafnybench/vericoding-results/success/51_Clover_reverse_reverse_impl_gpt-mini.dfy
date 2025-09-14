

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[n - 1 - j]) && a[n - 1 - j] == old(a[j])
    invariant forall j :: i <= j && j <= n - 1 - i ==> a[j] == old(a[j])
    decreases n - 2 * i
  {
    var tmp := a[i];
    a[i] := a[n - 1 - i];
    a[n - 1 - i] := tmp;
    i := i + 1;
  }
}
// </vc-code>

