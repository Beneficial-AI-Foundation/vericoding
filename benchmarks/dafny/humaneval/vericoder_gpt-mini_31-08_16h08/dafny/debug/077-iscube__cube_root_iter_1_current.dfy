

// <vc-helpers>
lemma cube_increasing(x: nat, y: nat)
  requires x < y
  ensures cube(x) < cube(y)
{
  // cube(y) - cube(x) = (y-x) * (y*y + y*x + x*x)
  assert cube(y) - cube(x) == (y - x) * (y*y + y*x + x*x);
  assert y - x > 0;
  assert y >= 1; // since x < y and x >= 0
  assert y*y + y*x + x*x >= 1; // y*y >= 1
  assert (y - x) * (y*y + y*x + x*x) > 0;
  assert cube(y) - cube(x) > 0;
}

lemma cube_Nplus1_gt_N(N: nat)
  ensures cube(N + 1) > N
{
  // Expand (N+1)^3 - N = N^3 + 3N^2 + 2N + 1 >= 1
  assert cube(N + 1) - N == N*N*N + 3*N*N + 2*N + 1;
  assert N*N*N + 3*N*N + 2*N + 1 >= 1;
  assert cube(N + 1) - N >= 1;
  assert cube(N + 1) > N;
}

lemma cube_leq_implies_leq_index(m: nat, N: nat)
  requires cube(m) <= N
  ensures m <= N
{
  if m >= N + 1 {
    if m == N + 1 {
      assert cube(m) == cube(N + 1);
    } else {
      // m > N + 1
      call cube_increasing(N + 1, m);
      assert cube(N + 1) < cube(m);
    }
    call cube_Nplus1_gt_N(N);
    assert cube(m) > N; // contradicts cube(m) <= N
    // unreachable, but keeps the verifier satisfied for the branch
  } else {
    // m < N+1 implies m <= N
    assert m <= N;
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
  var low: nat := 0;
  var high: nat := N + 1;
  // Initialize invariant: cube(low) <= N < cube(high)
  call cube_Nplus1_gt_N(N);
  assert cube(low) <= N;
  assert cube(high) > N;

  while low + 1 < high
    invariant 0 <= low <= high <= N + 1
    invariant cube(low) <= N
    invariant N < cube(high)
    invariant low <= N
    decreases high - low
  {
    var mid: nat := low + (high - low) / 2;
    if cube(mid) <= N {
      // update low; need to show mid <= N to maintain low <= N
      call cube_leq_implies_leq_index(mid, N);
      low := mid;
    } else {
      high := mid;
    }
  }
  r := low;
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