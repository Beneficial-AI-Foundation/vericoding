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
  /* code modified by LLM (iteration 2): fixed compilation error by using .Floor for truncation */
  i := x.Floor as real;
}
// </vc-code>
