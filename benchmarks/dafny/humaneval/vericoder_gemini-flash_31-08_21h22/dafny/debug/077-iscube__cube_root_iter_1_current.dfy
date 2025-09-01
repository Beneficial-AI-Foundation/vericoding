

// <vc-helpers>
function cube(n: nat): nat { n * n * n }
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

  while low <= high
    invariant 0 <= low
    invariant high <= N // high is always <= initial N (which is N for this loop)
    invariant cube(low) <= N // This is the key invariant that low always satisfies, ensuring cube(low) is not too large
    invariant (cube(high + 1) > N || high == N) // This ensures that for all values high can take, cube(high+1) is either > N, or high is N (meaning high can't go higher)
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    var c_mid := cube(mid);

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
      high := mid - 1; // mid is too large, try lower
    }
  }
  // At This point, low > high.
  // The loop invariant cube(low_at_start) <= N and cube(high_at_start + 1) > N (implied by high being reduced)
  // When the loop terminates low = high + 1
  // We want to return r such that cube(r) <= N < cube(r + 1)
  // From the invariants:
  // For the last `low` value: cube(low-1) <= N (because low was `mid+1`, and the previous `mid` had cube(mid) <= N)
  // For the last `high` value: cube(high+1) > N (because high was `mid-1`, and the previous `mid` had cube(mid) > N)
  // Since low = high + 1 at termination, it means cube(high) <= N and cube(high+1) > N.
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