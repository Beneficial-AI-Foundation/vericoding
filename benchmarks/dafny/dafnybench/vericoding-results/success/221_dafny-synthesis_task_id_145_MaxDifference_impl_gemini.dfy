// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int { if a > b then a else b }
function min(a: int, b: int): int { if a < b then a else b }
// </vc-helpers>

// <vc-spec>
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
// </vc-spec>
// <vc-code>
{
  var min_val := a[0];
  var max_val := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> min_val <= a[k] && a[k] <= max_val
    invariant exists k :: 0 <= k < i && a[k] == min_val
    invariant exists k :: 0 <= k < i && a[k] == max_val
  {
    min_val := min(min_val, a[i]);
    max_val := max(max_val, a[i]);
    i := i + 1;
  }
  diff := max_val - min_val;
}
// </vc-code>
