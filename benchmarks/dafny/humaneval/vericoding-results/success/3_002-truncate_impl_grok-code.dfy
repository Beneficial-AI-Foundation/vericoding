// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method truncate(x : real) returns (i : real)

    requires x >= 0.0

    ensures (0.0 <= x - i < 1.0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Added loop invariants to ensure verification of postcondition */
  var n: real := 0.0;
  while n + 1.0 <= x
    invariant 0.0 <= n
    invariant n <= x
  {
    n := n + 1.0;
  }
  return n;
}
// </vc-code>
