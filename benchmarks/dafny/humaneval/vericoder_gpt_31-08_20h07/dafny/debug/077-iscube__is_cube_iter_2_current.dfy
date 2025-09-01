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
    invariant !r ==> forall t: nat :: t < i ==> n != cube(t)
    decreases n - i + 1
  {
    if cube(i) == n {
      r := true;
      w := i;
    } else {
      assert forall t: nat | t < i + 1 :: n != cube(t) by {
        if t < i {
          assert !r;
          assert 0 <= t;
          assert t < i;
          assert n != cube(t);
        } else {
          assert i <= t;
          assert t < i + 1;
          assert t == i;
          assert n != cube(i);
        }
      }
      i := i + 1;
    }
  }
  if r {
    assert 0 <= w <= n && n == cube(w);
  } else {
    assert i > n;
    assert forall t: nat | t <= n :: n != cube(t) by {
      assert t <= n;
      assert i > n;
      assert t < i;
      assert !r;
      assert n != cube(t);
    }
  }
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end