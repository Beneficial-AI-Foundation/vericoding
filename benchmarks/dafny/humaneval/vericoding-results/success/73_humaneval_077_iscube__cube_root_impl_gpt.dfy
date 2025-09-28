// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
lemma lemma_cube_ge_self(k: nat)
  ensures k <= cube(k)
{
  if k == 0 {
    assert k <= cube(k);
  } else {
    assert k == k * 1;
    assert 1 <= k;
    assert k * 1 <= k * k;
    assert k * k == (k * k) * 1;
    assert (k * k) * 1 <= (k * k) * k;
    assert k <= k * k * k;
  }
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
    invariant r <= N
    invariant cube(r) <= N
    decreases N - r
  {
    var k: nat := r + 1;
    assert cube(k) <= N;
    lemma_cube_ge_self(k);
    assert k <= N;
    r := k;
  }
}
// </vc-code>
