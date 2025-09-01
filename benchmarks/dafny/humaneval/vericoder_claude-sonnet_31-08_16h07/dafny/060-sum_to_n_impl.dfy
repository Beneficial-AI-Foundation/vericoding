

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
  if n <= 0 {
    r := 0;
  } else {
    r := 0;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant r == (i - 1) * i / 2
    {
      r := r + i;
      i := i + 1;
    }
  }
}
// </vc-code>

