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
  /* code modified by LLM (iteration 3): convert floor result to real type */
  var floor_x := x.Floor;
  i := floor_x as real;
}
// </vc-code>
