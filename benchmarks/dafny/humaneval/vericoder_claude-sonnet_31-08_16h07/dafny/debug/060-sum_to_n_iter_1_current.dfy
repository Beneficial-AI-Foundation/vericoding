

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)
  // post-conditions-start
  ensures r == n * (n + 1) / 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant r == i * (i - 1) / 2
  {
    r := r + i;
    i := i + 1;
  }
}
// </vc-code>

