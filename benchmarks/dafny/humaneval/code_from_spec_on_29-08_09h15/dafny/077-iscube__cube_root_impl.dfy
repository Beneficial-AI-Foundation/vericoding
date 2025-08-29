

// <vc-helpers>
lemma cube_monotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
  if a == b {
    assert cube(a) == cube(b);
  } else {
    assert a < b;
    assert a * a <= b * b;
    assert a * a * a <= b * b * b;
  }
}

lemma cube_strictly_increasing(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
  assert a < b;
  assert a * a < b * b;
  assert a * a * a < b * b * b;
}

lemma cube_root_bounds(r: nat, N: nat)
  requires cube(r) <= N < cube(r + 1)
  ensures r <= N
{
  if r == 0 {
    assert r <= N;
  } else {
    assert r >= 1;
    assert cube(r) >= r;
    assert N >= cube(r) >= r;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method cube_root(N: nat) returns (r: nat)
Find the integer cube root. Ensures: the result r is the largest integer such that r³ ≤ N < (r+1)³; the result is at most N.
*/
// </vc-description>

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
  assert cube(r + 1) > N;
  cube_root_bounds(r, N);
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