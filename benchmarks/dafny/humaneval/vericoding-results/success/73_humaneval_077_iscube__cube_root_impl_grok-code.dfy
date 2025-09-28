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
  /* code modified by LLM (iteration 3): Added loop invariant to prove postconditions. */
  r := 0;
  while cube(r + 1) <= N
    invariant 0 <= r && cube(r) <= N
    decreases N - r
  {
    r := r + 1;
  }
}
// </vc-code>
