// <vc-helpers>
lemma CubeRootProperties(r: nat, N: nat)
  requires cube(r) <= N < cube(r + 1)
  ensures forall k :: k > r ==> cube(k) > N
  ensures forall k :: k < r && cube(k) <= N ==> cube(k) < cube(r)
{
  forall k | k > r
    ensures cube(k) > N
  {
    if k == r + 1 {
      // Direct from precondition
    } else {
      // k >= r + 2, so cube(k) >= cube(r + 1) > N
      CubeMonotonic(r + 1, k);
    }
  }
}

lemma CubeMonotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
  if a == b {
    // trivial
  } else if a + 1 == b {
    // cube(a+1) = (a+1)³ = a³ + 3a² + 3a + 1 >= a³
  } else {
    // induction using intermediate values
    CubeMonotonic(a, b - 1);
    CubeMonotonic(b - 1, b);
  }
}

lemma CubeRootUnique(r1: nat, r2: nat, N: nat)
  requires cube(r1) <= N < cube(r1 + 1)
  requires cube(r2) <= N < cube(r2 + 1)
  ensures r1 == r2
{
  if r1 < r2 {
    CubeMonotonic(r1 + 1, r2);
    assert cube(r1 + 1) <= cube(r2) <= N;
    assert false;
  } else if r2 < r1 {
    CubeMonotonic(r2 + 1, r1);
    assert cube(r2 + 1) <= cube(r1) <= N;
    assert false;
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
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
// </vc-spec>
// <vc-code>
{
  r := 0;
  while cube(r + 1) <= N
    invariant cube(r) <= N
    invariant r <= N
    decreases N - cube(r)
  {
    r := r + 1;
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