// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

function ComputeSquare(n: int): int
  requires n >= 0
  ensures ComputeSquare(n) == n * n
{
  if n == 0 then 0 else ComputeSquare(n - 1) + 2*n - 1
}

// </vc-helpers>

// <vc-spec>
method car_race_collision(n: int) returns (cnt: int)

  requires n >= 0

  ensures cnt == n * n
// </vc-spec>
// <vc-code>
{
  cnt := ComputeSquare(n);
}
// </vc-code>
