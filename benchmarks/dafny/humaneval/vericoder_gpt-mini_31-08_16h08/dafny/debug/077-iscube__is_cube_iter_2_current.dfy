method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma cube_monotone(a: int, b: int)
  requires 0 <= a < b
  ensures cube(a) < cube(b)
{
  // b^3 - a^3 = (b-a)*(b^2 + b*a + a^2)
  assert cube(b) - cube(a) == (b - a) * (b*b + b*a + a*a);
  assert b - a > 0;
  // from a < b and a >= 0 (since a >= 0 by requires) we get b > 0, hence b*b + b*a + a*a > 0
  assert b > 0;
  assert b*b + b*a + a*a > 0;
  assert (b - a) * (b*b + b*a + a*a) > 0;
  assert cube(b) - cube(a) > 0;
}
// </vc-helpers>

// <vc-spec>
method is_cube(n: nat) returns (r: bool)
  // pre-conditions-start
  // pre-conditions-end
  // post-conditions-start
  ensures r ==> exists r :: 0 <= r <= n && n == cube(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube(r)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i: nat := 0;
  while i <= n && cube(i) <= n
    invariant 0 <= i <= n + 1
    invariant forall k :: 0 <= k < i ==> cube(k) != n
    decreases n - i
  {
    if cube(i) == n {
      var k := i;
      assert 0 <= k <= n;
      assert cube(k) == n;
      return true;
    }
    i := i + 1;
  }
  // At this point either i > n or cube(i) > n.
  if i > n {
    // then for every k with 0 <= k <= n we have k < i, so the loop invariant gives cube(k) != n
    assert forall k :: 0 <= k <= n ==> cube(k) != n;
  } else {
    // i <= n and loop exited, so cube(i) > n
    assert cube(i) > n;
    // For any k in [0..n]:
    // - if k < i then loop invariant gives cube(k) != n
    // - if k == i then cube(i) > n so cube(k) != n
    // - if k > i then i < k <= n and by monotonicity cube(k) > cube(i) > n
    assert forall k :: 0 <= k <= n ==>
      if k < i then cube(k) != n
      else if k == i then cube(k) != n
      else cube(k) > n;
    assert forall k :: 0 <= k <= n ==> cube(k) != n;
  }
  return false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end