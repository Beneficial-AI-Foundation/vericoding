method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function cube_val(n: int): int { n * n * n }

lemma CubeMonotonic(a: nat, b: nat)
  ensures a <= b ==> cube_val(a) <= cube_val(b)
{
  if a <= b {
    var d := b - a;
    assert b == a + d;
    assert cube_val(b) == cube_val(a + d) == (a + d) * (a + d) * (a + d);
    assert cube_val(a + d) == a*a*a + 3*a*a*d + 3*a*d*d + d*d*d;
    assert cube_val(a) == a*a*a;
    assert cube_val(b) >= cube_val(a);
  }
}

lemma CubeRootExists(n: nat)
  ensures exists r :: 0 <= r <= n && cube_val(r) <= n < cube_val(r + 1)
{
  var r := 0;
  while r <= n && cube_val(r) <= n
    invariant 0 <= r <= n + 1
    invariant forall k :: 0 <= k < r ==> cube_val(k) <= n < cube_val(k + 1) || cube_val(k) > n
  {
    if cube_val(r + 1) > n {
      assert cube_val(r) <= n < cube_val(r + 1);
      return;
    }
    r := r + 1;
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
method is_cube(n: nat) returns (r: bool)
  ensures r ==> exists r :: 0 <= r <= n && n == cube_val(r)
  ensures !r ==> forall r :: 0 <= r <= n ==> n != cube_val(r)
{
  var res := 0;
  while res <= n
    invariant 0 <= res <= n + 1
    invariant forall k :: 0 <= k < res ==> cube_val(k) <= n < cube_val(k + 1) || cube_val(k) > n
    decreases n - res
  {
    if cube_val(res) > n {
      return false;
    } else if cube_val(res) == n {
      return true;
    }
    res := res + 1;
  }
  return false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end