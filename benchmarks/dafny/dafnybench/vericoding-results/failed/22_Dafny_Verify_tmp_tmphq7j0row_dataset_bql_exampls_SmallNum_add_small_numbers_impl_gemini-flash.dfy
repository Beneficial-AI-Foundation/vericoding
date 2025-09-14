

// <vc-helpers>
lemma lemma_add_nonnegative(x: int, y: int) returns (s: int)
  requires x >= 0;
  requires y >= 0;
  ensures s >= 0
{
  s := x + y;
}
// </vc-helpers>

// <vc-spec>
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// </vc-spec>
// <vc-code>
{
  var current_sum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n;
    invariant 0 <= current_sum;
    invariant (forall j: int :: 0 <= j && j < i ==> a[j] <= max);
    invariant current_sum <= max * i;
  {
    current_sum := current_sum + a[i];
    i := i + 1;
  }
  return current_sum;
}
// </vc-code>

