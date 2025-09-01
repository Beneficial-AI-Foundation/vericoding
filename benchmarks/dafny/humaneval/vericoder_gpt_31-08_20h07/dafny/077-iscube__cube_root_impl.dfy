

// <vc-helpers>
lemma cube_ge_self(n: nat)
  ensures n <= cube(n)
{
  if n == 0 {
    assert 0 <= cube(0);
  } else {
    assert n >= 1;
    // Show n <= n*n
    assert n * (n - 1) >= 0;
    assert n*n - n == n * (n - 1);
    assert n <= n*n;

    // Show n*n <= n*n*n
    assert n*n * (n - 1) >= 0;
    assert n*n*n - n*n == n*n * (n - 1);
    assert n*n <= n*n*n;

    assert n <= n*n*n;
    assert n <= cube(n);
  }
}
// </vc-helpers>

// <vc-spec>
method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  r := 0;
  while cube(r + 1) <= N
    invariant 0 <= r <= N
    invariant cube(r) <= N
    decreases N - r
  {
    var newr := r + 1;
    assert cube(newr) <= N; // from loop guard
    cube_ge_self(newr);
    assert newr <= cube(newr);
    assert newr <= N;
    r := newr;
  }
}
// </vc-code>

method is_cube(n: nat) returns (r: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
  // post-conditions-end
{
  assume{:axiom} false;
}
function cube(n: int): int { n * n * n }
// pure-end