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

lemma binary_search_lemma(N: nat, r: nat)
  requires cube(r) <= N < cube(r + 1)
  ensures (cube(r) == N) <==> (exists k :: 0 <= k <= N && N == cube(k))
  ensures (cube(r) != N) <==> (forall k :: 0 <= k <= N ==> N != cube(k))
{
  if cube(r) == N {
    // The positive case is straightforward: r itself is the witness
    assert exists k :: 0 <= k <= N && N == cube(k);
  } else {
    // Need to show no cube equals N
    // By the postcondition of binary_search_cube_root, we know:
    // cube(r) <= N < cube(r + 1) and cube(r) != N
    // So: cube(r) < N < cube(r + 1)
    
    // By cube_increasing and cube_monotonic, all cubes are strictly increasing
    // So any k <= r gives cube(k) <= cube(r) < N
    // And any k >= r+1 gives cube(k) >= cube(r+1) > N
    // Thus no integer k can satisfy cube(k) == N
    forall k | 0 <= k <= N
      ensures N != cube(k)
    {
      if k <= r {
        assert cube(k) <= cube(r);
        assert cube(r) < N;
        assert cube(k) < N;
      } else {
        assert k >= r + 1;
        assert cube(k) >= cube(r + 1);
        assert N < cube(r + 1);
        assert N < cube(k);
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
  if n == 0 {
    return true;
  }
  var root := binary_search_cube_root(n);
  binary_search_lemma(n, root);
  return cube(root) == n;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end