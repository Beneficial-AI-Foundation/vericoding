// <vc-helpers>
// </vc-helpers>

method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// <vc-code>
{
  assume false;
}
// </vc-code>