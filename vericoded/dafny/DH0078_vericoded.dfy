// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method cube_root(N: nat) returns (r: nat)

  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
// </vc-spec>
// <vc-code>
{
  r := 0;
  while cube(r + 1) <= N
    invariant cube(r) <= N
    invariant r <= N
  {
    r := r + 1;
  }
}
// </vc-code>
