

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var mn := a[0];
  var mx := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant forall k :: 0 <= k < i ==> mn <= a[k] <= mx
    decreases n - i
  {
    if a[i] < mn {
      mn := a[i];
    }
    if a[i] > mx {
      mx := a[i];
    }
    i := i + 1;
  }
  diff := mx - mn;
}
// </vc-code>

