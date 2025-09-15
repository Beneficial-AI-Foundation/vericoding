// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function square(n: int): int { n * n }
// </vc-helpers>

// <vc-spec>
method car_race_collision(n: int) returns (cnt: int)

  requires n >= 0

  ensures cnt == n * n
// </vc-spec>
// <vc-code>
{
  cnt := square(n);
}
// </vc-code>
