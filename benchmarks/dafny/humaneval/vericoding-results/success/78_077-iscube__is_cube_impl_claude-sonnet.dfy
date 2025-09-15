// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added witness lemma for cube root existence */
predicate IsCube(n: nat, root: nat)
{
  root * root * root == n
}

lemma CubeMonotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
}

lemma CubeStrictlyIncreasing(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
}

lemma CubeBounds(n: nat, r: nat)
  requires cube(r) > n
  ensures forall k :: k >= r ==> cube(k) > n
{
}

lemma CubeUpperBound(n: nat)
  ensures forall k :: k > n ==> cube(k) > n
{
}

lemma CubeUniqueness(n: nat, a: nat, b: nat)
  requires cube(a) == n && cube(b) == n
  ensures a == b
{
  if a != b {
    if a < b {
      CubeStrictlyIncreasing(a, b);
      assert cube(a) < cube(b);
      assert false;
    } else {
      CubeStrictlyIncreasing(b, a);
      assert cube(b) < cube(a);
      assert false;
    }
  }
}

lemma CubeRangeComplete(n: nat, i: nat)
  requires cube(i) > n
  requires forall k :: 0 <= k < i ==> cube(k) != n
  ensures forall k :: 0 <= k <= n ==> cube(k) != n
{
  forall k | 0 <= k <= n
  ensures cube(k) != n
  {
    if k < i {
      // Already covered by precondition
    } else {
      // k >= i and cube(i) > n
      CubeBounds(n, i);
      assert cube(k) > n;
    }
  }
}

lemma CubeWitness(n: nat, i: nat)
  requires cube(i) == n
  requires 0 <= i <= n
  ensures exists r :: 0 <= r <= n && n == cube(r)
{
  assert 0 <= i <= n && n == cube(i);
}
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)

  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added witness lemma call to establish postcondition */
{
  if n == 0 {
    CubeWitness(n, 0);
    r := true;
    return;
  }
  
  var i := 0;
  while i <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> cube(k) != n
    decreases n - i + 1
  {
    if cube(i) == n {
      CubeWitness(n, i);
      r := true;
      return;
    }
    if cube(i) > n {
      CubeRangeComplete(n, i);
      r := false;
      return;
    }
    i := i + 1;
  }
  
  // i == n + 1, so we've checked all k where 0 <= k <= n
  assert forall k :: 0 <= k <= n ==> cube(k) != n;
  r := false;
}
// </vc-code>
