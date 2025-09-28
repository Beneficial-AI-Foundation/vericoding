// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SquareRoot(n: nat) returns (result: nat)
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>

/* code modified by LLM (iteration 3): Fixed loop invariants by setting high to n+1 and adjusted invariants accordingly */
{
  if n == 0 {
    result := 0;
  } else {
    var low: nat := 0;
    var high: nat := n + 1;
    while low + 1 < high
      invariant 0 <= low && 0 < high && low < high && high <= n + 1
      invariant low * low <= n
      invariant n < high * high
      decreases high - low
    {
      var mid: nat := low + (high - low) / 2;
      if mid * mid <= n {
        low := mid;
      } else {
        high := mid;
      }
    }
    result := low;
  }
}

// </vc-code>
