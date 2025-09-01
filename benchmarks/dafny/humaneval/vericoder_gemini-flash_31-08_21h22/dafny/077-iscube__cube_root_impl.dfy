

// <vc-helpers>
function cube_nat(n: nat): nat { n * n * n }
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
  var high: nat := N;

  if (N == 0) {
    return 0;
  }

  while low <= high
    invariant 0 <= low
    invariant low <= N + 1
    invariant high <= N
    invariant cube_nat(low) <= N || (low == 0 && N == 0)
    invariant (high == N || cube_nat(high + 1) > N)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    var c_mid := cube_nat(mid);

    if c_mid == N
    {
      return mid;
    }
    else if c_mid < N
    {
      low := mid + 1;
    }
    else // c_mid > N
    {
      high := mid - 1;
    }
  }

  return high;
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