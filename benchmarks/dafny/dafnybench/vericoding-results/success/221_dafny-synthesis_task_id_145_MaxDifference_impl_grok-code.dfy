

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
  var min := a[0];
  var max := a[0];
  var i := 1;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant min in a[..i]
    invariant forall j :: 0 <= j < i ==> a[j] >= min
    invariant max in a[..i]
    invariant forall j :: 0 <= j < i ==> a[j] <= max
  {
    if a[i] < min { min := a[i]; }
    if a[i] > max { max := a[i]; }
    i := i + 1;
  }
  diff := max - min;
}
// </vc-code>

