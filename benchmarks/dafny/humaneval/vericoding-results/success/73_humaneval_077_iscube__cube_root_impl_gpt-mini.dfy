// <vc-preamble>
function cube(n: int): int { n * n * n }
// </vc-preamble>

// <vc-helpers>
lemma cube_strict_increasing(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
  decreases b - a
{
  if a + 1 == b {
    assert cube(a+1) - cube(a) == 3*a*a + 3*a + 1;
    assert 3*a*a + 3*a + 1 >= 1;
    assert cube(a+1) > cube(a);
  } else {
    cube_strict_increasing(a, b-1);
    cube_strict_increasing(b-1, b);
    assert cube(a) < cube(b);
  }
}

lemma cube_Nplus1_gt_N(N: nat)
  ensures cube(N+1) > N
{
  assert N + 1 >= 1;
  assert (N+1)*(N+1) >= 1;
  assert cube(N+1) == (N+1)*((N+1)*(N+1));
  assert cube(N+1) >= (N+1)*1;
  assert cube(N+1) >= N+1;
  assert N+1 > N;
  assert cube(N+1) > N;
}
// </vc-helpers>

// <vc-spec>
method cube_root(N: nat) returns (r: nat)

  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
// </vc-spec>
// <vc-code>
{
  var low: nat := 0;
  var high: nat := N + 1;
  while low + 1 < high
    invariant 0 <= low <= high <= N + 1
    invariant cube(low) <= N < cube(high)
    decreases high - low
  {
    var mid: nat := (low + high) / 2;
    if cube(mid) <= N {
      low := mid;
    } else {
      high := mid;
    }
  }
  r := low;
}
// </vc-code>
