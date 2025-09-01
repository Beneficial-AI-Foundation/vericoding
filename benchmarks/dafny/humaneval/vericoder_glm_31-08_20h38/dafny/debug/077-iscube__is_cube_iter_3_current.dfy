method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma cube_monotonic(n: nat, m: nat)
  requires n <= m
  ensures cube(n) <= cube(m)
{
  calc {
    cube(m);
    m * m * m;
    >= {assert m >= n; assert m >= 0;} n * m * m;
    >= {assert m >= n; assert n >= 0;} n * n * m;
    >= {assert m >= n; assert n >= 0;} n * n * n;
    cube(n);
  }
}

lemma cube_increasing(n: nat)
  ensures cube(n) < cube(n + 1)
{
  calc {
    cube(n + 1);
    (n + 1) * (n + 1) * (n + 1);
    == (n * n + 2 * n + 1) * (n + 1);
    n * n * (n + 1) + (2 * n + 1) * (n + 1);
    == n * n * n + n * n + 2 * n * (n + 1) + (n + 1);
    == cube(n) + (n * n + 2 * n * n + 2 * n + n + 1);
    == cube(n) + (3 * n * n + 3 * n + 1);
    > cube(n);
  }
}

method binary_search_cube_root(N: nat) returns (r: nat)
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
{
  var low, high := 0, N+1;
  while low + 1 < high
    invariant 0 <= low < high <= N+1
    invariant cube(low) <= N < cube(high)
  {
    var mid := (low + high) / 2;
    if cube(mid) <= N {
      low := mid;
    } else {
      high := mid;
    }
  }
  return low;
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
  var root := binary_search_cube_root(n);
  return cube(root) == n;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end