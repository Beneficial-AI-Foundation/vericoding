// SPEC
method MaxDifference(a: array<int>) returns (diff: int)
  requires a.Length > 1
  ensures forall i, j :: 0 <= i < a.Length && 0 <= j < a.Length ==> a[i] - a[j] <= diff
{
}
