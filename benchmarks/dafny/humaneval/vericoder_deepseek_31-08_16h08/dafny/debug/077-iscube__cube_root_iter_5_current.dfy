

// <vc-helpers>
lemma CubeMonotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
}

lemma CubeDifference(r: nat)
  ensures cube(r + 1) - cube(r) == 3*r*r + 3*r + 1
{
}

lemma CubeNonNegative(n: nat)
  ensures cube(n) >= 0
{
}

predicate IsCube(n: nat, r: nat)
{
  n == cube(r)
}

lemma CubeRootExists(n: nat)
  ensures exists r: nat :: r <= n && cube(r) <= n < cube(r + 1)
{
  if n == 0 {
    assert cube(0) <= 0 < cube(1);
  } else {
    var r := 0;
    while r <= n
      invariant r >= 0
      invariant cube(r) <= n
    {
      if n < cube(r + 1) {
        return;
      }
      r := r + 1;
    }
  }
}

lemma CubeMonotonicInt(a: int, b: int)
  requires 0 <= a <= b
  ensures cube(a) <= cube(b)
{
}

lemma CubePreservesNat(n: nat)
  ensures cube(n) >= 0
{
}

lemma CubeStrictlyIncreasing(n: nat)
  ensures cube(n + 1) > cube(n)
{
}

lemma CubeBinarySearchHelper(low: nat, high: nat, N: nat)
  requires low <= high <= N
  requires cube(low) <= N
  requires N < cube(high + 1)
  ensures forall mid: nat :: mid >= low && mid <= high ==> cube(mid) <= cube(high)
{
  var mid := low;
  while mid <= high
    invariant low <= mid <= high + 1
    invariant forall i: nat :: i >= low && i < mid ==> cube(i) <= cube(high)
  {
    if mid < high {
      CubeMonotonic(mid, high);
    }
    mid := mid + 1;
  }
}

lemma CubeBinarySearchInvariant(low: nat, high: nat, N: nat)
  requires low <= high <= N
  requires cube(low) <= N
  requires N < cube(high + 1)
  ensures cube(high) > N ==> (high > 0 && N < cube(high))
  ensures cube(high) <= N ==> (high < N && cube(high + 1) > N)
{
}
// </vc-helpers>
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
  if N == 0 {
    return 0;
  }
  
  var low := 0;
  var high := N;
  
  while low < high
    invariant low <= high <= N
    invariant cube(low) <= N
    invariant N < cube(high + 1)
    decreases high - low
  {
    var mid := (low + high) / 2;
    CubeBinarySearchHelper(low, high, N);
    if cube(mid) <= N {
      low := mid + 1;
      CubeBinarySearchInvariant(low, high, N);
    } else {
      high := mid;
      CubeBinarySearchInvariant(low, high, N);
    }
  }
  
  assert low > 0;
  r := low - 1;
  
  assert cube(r) <= N;
  assert cube(r + 1) > N;
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