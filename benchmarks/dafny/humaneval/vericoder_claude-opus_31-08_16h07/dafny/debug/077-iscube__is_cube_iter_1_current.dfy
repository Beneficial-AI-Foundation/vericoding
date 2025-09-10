method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma cube_monotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
  if a == b {
    // trivial
  } else {
    assert a < b;
    assert a * a <= b * b;
    assert a * a * a <= b * b * b;
  }
}

lemma no_cube_between(r: nat, n: nat)
  requires cube(r) < n < cube(r + 1)
  ensures forall k :: 0 <= k <= n ==> n != cube(k)
{
  forall k | 0 <= k <= n
    ensures n != cube(k)
  {
    if k <= r {
      cube_monotonic(k, r);
      assert cube(k) <= cube(r) < n;
    } else if k >= r + 1 {
      cube_monotonic(r + 1, k);
      assert n < cube(r + 1) <= cube(k);
    }
  }
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
  var root := cube_root(n);
  
  if cube(root) == n {
    r := true;
    assert n == cube(root);
    assert 0 <= root <= n;
  } else {
    r := false;
    assert cube(root) < n < cube(root + 1);
    no_cube_between(root, n);
  }
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end