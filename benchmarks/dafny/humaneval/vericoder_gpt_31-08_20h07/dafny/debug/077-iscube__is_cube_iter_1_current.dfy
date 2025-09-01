method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>

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
  var w: nat := 0;
  r := false;
  while i <= n && !r
    invariant 0 <= i <= n + 1
    invariant r ==> 0 <= w <= n && n == cube(w)
    invariant !r ==> forall t :: 0 <= t < i ==> n != cube(t)
    decreases n - i + 1
  {
    if cube(i) == n {
      r := true;
      w := i;
    } else {
      assert forall t :: 0 <= t < i + 1 ==> n != cube(t) {
        if t < i {
        } else {
          assert t <= i;
          assert i <= t;
          assert t == i;
          assert n != cube(i);
        }
      }
      i := i + 1;
    }
  }
  if r {
    assert 0 <= w <= n && n == cube(w);
    assert exists k :: 0 <= k <= n && n == cube(k) by {
      assert 0 <= w <= n && n == cube(w);
    }
  } else {
    assert i > n;
    assert forall t :: 0 <= t <= n ==> n != cube(t) {
      assert t < i;
    }
  }
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end