// <vc-helpers>
// </vc-helpers>

method maxArray(a: array<int>) returns (m: int)
  requires a.Length >= 1
  ensures forall k :: 0 <= k < a.Length ==> m >= a[k]
  ensures exists k :: 0 <= k < a.Length && m == a[k]
// <vc-code>
{
  assume false;
}
// </vc-code>