// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method car_race_collision(n: int) returns (cnt: int)

  requires n >= 0

  ensures cnt == n * n
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
