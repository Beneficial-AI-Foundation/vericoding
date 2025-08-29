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
  if a == 0 {
    assert cube(a) == 0;
    assert cube(b) > 0;
  } else {
    assert a * a < b * b;
    assert a * a * a < b * b * b;
  }
}

lemma cube_root_witnesses_existence(n: nat, root: nat)
  requires cube(root) <= n < cube(root + 1)
  requires cube(root) == n
  ensures exists r :: 0 <= r <= n && n == cube(r)
{
  assert 0 <= root <= n && n == cube(root);
}

lemma cube_root_proves_non_existence(n: nat, root: nat)
  requires cube(root) <= n < cube(root + 1)
  requires cube(root) != n
  ensures forall r :: 0 <= r <= n ==> n != cube(r)
{
  forall r | 0 <= r <= n
    ensures n != cube(r)
  {
    if r < root {
      cube_strictly_increasing(r, root);
      assert cube(r) < cube(root) <= n;
    } else if r == root {
      assert cube(r) == cube(root) != n;
    } else {
      assert r > root;
      if r >= root + 1 {
        cube_monotonic(root + 1, r);
        assert cube(r) >= cube(root + 1) > n;
      }
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method is_cube(n: nat) returns (r: bool)
Check if condition holds. Ensures: if true, then there exists an integer r such that N = r³; if false, then no integer r satisfies N = r³.
*/
// </vc-description>

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
    cube_root_witnesses_existence(n, root);
    r := true;
  } else {
    cube_root_proves_non_existence(n, root);
    r := false;
  }
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end