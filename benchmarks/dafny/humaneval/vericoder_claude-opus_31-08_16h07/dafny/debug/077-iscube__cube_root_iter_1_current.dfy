

// <vc-helpers>
lemma cube_monotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
  // Proof by Dafny's automatic verification
}

lemma cube_strictly_monotonic(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
  // For natural numbers, if a < b then a³ < b³
  if a == 0 {
    assert cube(0) == 0;
    assert b >= 1;
    assert cube(b) >= b;
  } else {
    // a >= 1 and b > a
    assert cube(a) == a * a * a;
    assert cube(b) == b * b * b;
    assert a * a < b * b;
    assert a * a * a < b * b * b;
  }
}

lemma cube_root_bounds(N: nat, r: nat)
  requires cube(r) <= N < cube(r + 1)
  ensures r <= N
{
  if r > N {
    assert r >= N + 1;
    cube_monotonic(N + 1, r);
    assert cube(N + 1) <= cube(r);
    assert cube(N + 1) == (N + 1) * (N + 1) * (N + 1);
    assert (N + 1) * (N + 1) * (N + 1) >= (N + 1) * 1 * 1;
    assert (N + 1) * 1 * 1 == N + 1;
    assert cube(N + 1) >= N + 1;
    assert cube(r) >= N + 1;
    assert cube(r) > N;
    assert false;
  }
}
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
  
  var low: nat := 0;
  var high: nat := N;
  
  while low < high
    invariant 0 <= low <= high <= N
    invariant cube(low) <= N
    invariant high < N ==> N < cube(high + 1)
  {
    var mid: nat := (low + high + 1) / 2;
    
    if cube(mid) <= N {
      low := mid;
    } else {
      high := mid - 1;
    }
  }
  
  r := low;
  
  // Prove the postconditions
  assert cube(r) <= N;
  
  if r < N {
    cube_strictly_monotonic(r, r + 1);
    if cube(r + 1) <= N {
      assert r + 1 <= N;
      assert low == high;
      assert r == low;
      assert false; // This case leads to contradiction
    }
  }
  
  cube_root_bounds(N, r);
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