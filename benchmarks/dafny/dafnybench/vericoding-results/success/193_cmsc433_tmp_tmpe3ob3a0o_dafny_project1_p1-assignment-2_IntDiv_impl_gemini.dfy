// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IntDiv (m : int, n : int) returns (d : int, r : int)
    requires n > 0
    ensures m == n * d + r && 0 <= r < n
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added `r < n` invariant to loop for negative m */
  if m >= 0 {
    d := 0;
    r := m;
    while r >= n
      invariant m == n * d + r && r >= 0
      decreases r
    {
      d := d + 1;
      r := r - n;
    }
  } else {
    d := 0;
    r := m;
    while r < 0
      invariant m == n * d + r && r < n
      decreases -r
    {
      d := d - 1;
      r := r + n;
    }
  }
}
// </vc-code>
