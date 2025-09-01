

// <vc-helpers>
function cube_nat(n: nat): nat { n * n * n }

// Helper function to find the maximum possible cube root
function find_max_r(N: nat): nat
  decreases N
{
  if N == 0 then 0
  else if N == 1 then 1
  else if cube_nat(N) <= N then N
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
    var high: nat := N;

    // Loop invariant: cube(low) <= N and (high == N || cube(high+1) > N)
    // Invariant also ensures that the cube root r (if it exists within the search space) is between low and high
    // 0 <= low <= high <= N
    while low <= high
        invariant 0 <= low
        invariant high <= N
        invariant low <= high + 1
        invariant cube_nat(low) <= N || (low == 0 && N == 0) // adjusted for N=0
        invariant (high == N || cube_nat(high) > N || low > high || cube_nat(high + 1) > N) // Adjust invariant for high
        invariant (forall x: nat :: (cube_nat(x) <= N < cube_nat(x + 1)) ==> low <= x)
        invariant (forall x: nat :: (cube_nat(x) <= N < cube_nat(x + 1)) ==> x <= high + 1) // Adjusted upper bound for x
    {
        var mid := low + (high - low) / 2;
        if mid > N && N != 0
        {
          // This case occurs if low is very large and high is also large, but N is small.
          // This can happen if N=0 and low and high are initialized to 0. Then mid = 0.
          // Or if N = 1, high = 1, low = 0 => mid = 0.
          // However, if high is small and N is large, this should not occur.
          // To be safe, if we get here, then mid is too large, so we set high to mid - 1.
          high := mid - 1;
        }
        else if cube_nat(mid) <= N
        {
            if mid == high || cube_nat(mid + 1) > N
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