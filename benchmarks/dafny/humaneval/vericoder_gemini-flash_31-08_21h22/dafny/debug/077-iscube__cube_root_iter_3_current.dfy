

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
  var high: nat := N; // A safe upper bound for the cube root is N itself, as N*N*N > N for N > 1

  // Handle the case where N itself is 0, since (high - 1) makes high negative.
  // Although `nat` disallows this in Dafny, it's good practice.
  // The loop invariant `high <= N` and `cube_nat(low) <= N` may not hold for N=0
  // if high is simply initialized to N. In this special case the loop does not run
  // and high is correctly returned as 0.
  if N == 0 {
    return 0;
  }

  while low <= high
    invariant 0 <= low
    invariant high <= N // high is always <= initial N (which is N for this loop)
    invariant low == 0 || cube_nat(low - 1) < N // This is the key invariant that low always satisfies, ensuring cube_nat(low-1) is not too large
    // The invariant cube_nat(high + 1) > N must be careful for `high = N`.
    // It's equivalent to saying that if we were to take high+1, its cube would be > N.
    // If high is N, and cube_nat(N+1) > N, then it holds.
    // If high is N, it also holds because we can't go higher than N anyway.
    invariant (high == N || cube_nat(high + 1) > N)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    var c_mid := cube_nat(mid);

    if c_mid == N
    {
      return mid; // Found exact cube root
    }
    else if c_mid < N
    {
      low := mid + 1; // mid is too small, try higher
    }
    else // c_mid > N
    {
      // Since high is nat, high - 1 could be problematic if high is 0.
      // However, N!=0 is handled above, and low starts at 0.
      // The condition c_mid > N means mid > 0 (unless N is 0, handled above)
      // So high will be at least mid - 1, which will be >= 0.
      high := mid - 1; // mid is too large, try lower
    }
  }
  // At This point, low > high.
  // The loop invariant cube_nat(low-1) < N and (high == N || cube_nat(high + 1) > N)
  // When the loop terminates, low = high + 1
  // We want to return r such that cube_nat(r) <= N < cube_nat(r + 1)
  // From the invariants:
  // For the last `low` value: cube_nat(low-1) < N (because low was `mid+1`, and the previous `mid` had cube_nat(mid) <= N)
  // Which simplifies to cube_nat(high) < N.
  // For the last `high` value: (high == N || cube_nat(high+1) > N)
  // Since low = high + 1 at termination, it means cube_nat(high) < N and cube_nat(high+1) > N.
  // So 'high' is the result we are looking for.
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