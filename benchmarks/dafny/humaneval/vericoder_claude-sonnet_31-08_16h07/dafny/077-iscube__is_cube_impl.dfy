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
  assert a * a <= b * b;
  assert a * a * a <= b * b * b;
}

lemma cube_strictly_increasing(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
  assert a < b;
  assert a * a < b * b;
  assert a * a * a < b * b * b;
}

lemma cube_root_properties(n: nat, root: nat)
  requires cube(root) <= n < cube(root + 1)
  ensures cube(root) == n <==> exists r :: 0 <= r <= n && n == cube(r)
  ensures cube(root) != n <==> forall r :: 0 <= r <= n ==> n != cube(r)
{
  if cube(root) == n {
    assert 0 <= root <= n && n == cube(root);
  } else {
    assert cube(root) < n < cube(root + 1);
    forall r | 0 <= r <= n 
      ensures n != cube(r)
    {
      if r <= root {
        cube_monotonic(r, root);
        assert cube(r) <= cube(root) < n;
      } else {
        assert r >= root + 1;
        cube_monotonic(root + 1, r);
        assert cube(r) >= cube(root + 1) > n;
      }
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
  cube_root_properties(n, root);
  if cube(root) == n {
    r := true;
  } else {
    r := false;
  }
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end