// <vc-helpers>
lemma cube_monotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
}

lemma cube_strictly_increasing(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
}

lemma cube_root_bounds(N: nat, r: nat)
  requires cube(r) <= N < cube(r + 1)
  ensures r <= N
{
  if r > N {
    assert cube(r) > cube(N) by { cube_strictly_increasing(N, r); }
    assert false;
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
    invariant cube(r) <= N
    invariant r <= N
    decreases N - r
  {
    r := r + 1;
  }
  
  assert cube(r) <= N;
  assert N < cube(r + 1);
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