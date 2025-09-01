method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma cube_monotone(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
  // b^3 - a^3 = (b-a)*(b^2 + b*a + a^2)
  assert cube(b) - cube(a) == (b - a) * (b*b + b*a + a*a);
  assert b - a > 0;
  // from a < b and a >= 0 (since a: nat) we get b > 0, hence b*b + b*a + a*a > 0
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
  while i <= N && cube(i) <= N
    invariant 0 <= i <= N + 1
    invariant forall k :: 0 <= k < i ==> cube(k) != N
    decreases N - i
  {
    if cube(i) == N {
      return true;
    }
    i := i + 1;
  }
  // At this point either i > N or cube(i) > N.
  // From the loop invariant and monotonicity of cube we can conclude there is no k in [0..N] with cube(k) == N.
  return false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end