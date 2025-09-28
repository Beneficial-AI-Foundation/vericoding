// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
predicate IsCubeRoot(r: nat, N: nat) { cube(r) <= N < cube(r + 1) }
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
    invariant 0 <= r
    invariant cube(r) <= N
    decreases N - cube(r)
  {
    r := r + 1;
  }
}
// </vc-code>
