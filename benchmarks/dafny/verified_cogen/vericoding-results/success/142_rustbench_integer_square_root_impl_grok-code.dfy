// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IntegerSquareRoot(n: int) returns (result: int)
    requires n >= 1
    ensures 0 <= result * result
    ensures result * result <= n
    ensures n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): removed invalid invariant that failed verification */
  var r := 0;
  while (r + 1) * (r + 1) <= n
    invariant 0 <= r && r * r <= n
    decreases n - r
  {
    r := r + 1;
  }
  result := r;
}
// </vc-code>
