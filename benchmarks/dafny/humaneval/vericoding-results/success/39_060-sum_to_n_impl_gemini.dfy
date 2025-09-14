// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sum_to_n(n: int) returns (r : int)

  ensures r == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
  r := 0;
  if n < 0 {
    // The formula n * (n + 1) / 2 is the sum of a sequence,
    // but for negative n, a loop is less intuitive. The direct formula works.
    r := n * (n + 1) / 2;
  } else {
    var i := 0;
    while i <= n
      invariant 0 <= i <= n + 1
      invariant r == (i - 1) * i / 2
    {
      r := r + i;
      i := i + 1;
    }
  }
}
// </vc-code>
