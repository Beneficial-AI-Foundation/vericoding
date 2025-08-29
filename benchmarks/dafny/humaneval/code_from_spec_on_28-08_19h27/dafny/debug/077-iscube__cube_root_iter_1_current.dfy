// <vc-helpers>
lemma CubeRootProperties(r: nat, N: nat)
  requires cube(r) <= N < cube(r + 1)
  ensures forall k :: k > r ==> cube(k) > N
  ensures forall k :: k < r && cube(k) <= N ==> cube(k) < cube(r)
{
}

lemma CubeMonotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
}

lemma CubeRootUnique(r1: nat, r2: nat, N: nat)
  requires cube(r1) <= N < cube(r1 + 1)
  requires cube(r2) <= N < cube(r2 + 1)
  ensures r1 == r2
{
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