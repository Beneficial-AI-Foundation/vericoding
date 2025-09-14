

// <vc-helpers>
lemma MaintainInvariant(i: int, sum: int, max: int, a_val: int)
  requires 0 <= i
  requires sum <= max * i
  requires a_val <= max
  ensures sum + a_val <= max * (i+1)
{
  calc {
    sum + a_val;
    <= max * i + a_val;
    <= max * i + max;
    == max * (i+1);
  }
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
  var sum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum <= max * i
  {
    MaintainInvariant(i, sum, max, a[i]);
    sum := sum + a[i];
    i := i + 1;
  }
  return sum;
}
// </vc-code>

