

// <vc-helpers>
function cube(n: nat): nat { n * n * n }

// Helper function to find the maximum possible cube root
function find_max_r(N: nat): nat
  decreases N
{
  if N == 0 then 0
  else if cube(N) <= N then N
  else find_max_r(N / 2)
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
    // Binary search approach to find the cube root
    var low: nat := 0;
    var high: nat := N; // N is an upper bound for the cube root given r <= N

    // Loop invariant: cube(low) <= N and (high == N || cube(high+1) > N)
    // Invariant also ensures that the cube root r (if it exists within the search space) is between low and high
    // 0 <= low <= high <= N
    while low <= high
        invariant 0 <= low <= N
        invariant 0 <= high <= N
        invariant cube(low) <= N
        invariant (high == N || low > high || cube(high + 1) > N) // Adjust invariant for high
        invariant forall x :: (cube(x) <= N < cube(x + 1)) ==> low <= x
        invariant forall x :: (cube(x) <= N < cube(x + 1)) ==> x <= high
    {
        var mid := low + (high - low) / 2;
        if mid > N then // mid can exceed N if N is small and low is 0, high is N. This limits mid to N.
            mid := N;

        if cube(mid) <= N
        {
            if cube(mid + 1) > N
            {
                r := mid;
                return;
            }
            else
            {
                low := mid + 1;
            }
        }
        else
        {
            high := mid - 1;
        }
    }

    // After the loop, low is the smallest number such that cube(low) > N,
    // or low is N+1 if no such number exists and the loop terminates with low = old(high) + 1.
    // The loop finds the r such that r^3 <= N < (r+1)^3.
    // When low becomes greater than high, the loop terminates.
    // At this point, `low` is the candidate for `r+1` and `high` is the candidate for `r`.
    // The last `mid` for which `cube(mid) <= N` must be `r`.
    // So, `r` should be `high` from previous iteration when the condition `cube(mid) <= N` was met,
    // and `cube(mid + 1) > N` was false, which led to `low = mid + 1`.

    // If the loop finishes, it means no 'mid' satisfied both conditions.
    // The correct `r` will be `high`.
    // Example: N=7.
    // low=0, high=7. mid=3. cube(3)=27 > 7. high=2.
    // low=0, high=2. mid=1. cube(1)=1 <= 7. cube(2)=8 > 7. r=1. return.

    // If N=0:
    // low=0, high=0. mid=0. cube(0)=0 <= 0. cube(1)=1 > 0. r=0. return.

    // If no return happened in the loop, 'r' should be 'high' at loop exit.
    // This case happens if N is so small that high becomes -1 (e.g. N = 0, mid = 0, high becomes -1)
    // or if the initial search space doesn't contain a valid r (which should not be the case for N >= 0).
    // The post-condition `r <= N` implies r is a `nat`.
    // Consider the case where the loop finishes.
    // The invariant implies that at loop termination, low = high + 1.
    // And from the invariant: cube(low) <= N and cube(high + 1) > N.
    // combined with cube(low) > N.
    // So if low = high + 1, then cube(high + 1) > N and cube(high) <= N.
    // Thus `high` is the desired `r`.
    r := high;
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