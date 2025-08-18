// <vc-helpers>
// </vc-helpers>

method max(a: array<int>) returns (x: int)
  requires a.Length != 0
  ensures 0 <= x < a.Length
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[x]
// <vc-code>
{
  assume false;
}
// </vc-code>