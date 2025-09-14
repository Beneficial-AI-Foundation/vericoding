// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed logic for d>=2 and d==1 */
  q := 0;
  r := n;
  if d >= 2 {
    while r >= d
      invariant n == q * d + r
      invariant r >= 0
      invariant d >= 2
      invariant 2 * q <= n - r
    {
      r := r - d;
      q := q + 1;
    }
  } else { // d == 1
    // For d=1, the postcondition `q <= n/2` becomes `n <= n/2` (since q=n, r=0 is the only way to satisfy d*q+r=n).
    // `n <= n/2` is only true for n<=0.
    // However, the precondition `n >= d` means `n >= 1`.
    // This is a contradiction in the specification for any input with d=1 and n>=1.
    // Dafny can't prove this branch, but the code for d>=2 is correct.
    // The only way forward is to write the code that correctly computes division for d=1,
    // even though it will fail the contradictory postcondition.
    q := n;
    r := 0;
  }
}
// </vc-code>
