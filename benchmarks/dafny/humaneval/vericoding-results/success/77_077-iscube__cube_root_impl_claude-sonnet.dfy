// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
function cube_is_monotonic_lemma(a: nat, b: nat): bool
  requires a <= b
  ensures cube(a) <= cube(b)
{
  a * a * a <= b * b * b
}

lemma cube_monotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
}

lemma cube_root_bound(r: nat, N: nat)
  requires cube(r) <= N < cube(r + 1)
  ensures r <= N
{
}
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
