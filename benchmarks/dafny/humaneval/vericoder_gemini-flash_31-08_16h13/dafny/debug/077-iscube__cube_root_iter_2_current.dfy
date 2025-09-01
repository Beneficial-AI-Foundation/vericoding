

// <vc-helpers>
function cube(n: nat): nat { n * n * n }

// Helper function to find the maximum possible cube root
function find_max_r(N: nat): nat
  decreases N
{
  if N == 0 then 0
  else if N == 1 then 1
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
    var high: nat := N;

    // Loop invariant: cube(low) <= N and (high == N || cube(high+1) > N)
    // Invariant also ensures that the cube root r (if it exists within the search space) is between low and high
    // 0 <= low <= high <= N
    while low <= high
        invariant 0 <= low
        invariant high <= N
        invariant low <= high + 1
        invariant cube(low) <= N || (low == 0 && N == 0) // adjusted for N=0
        invariant (high == N || cube(high) > N || low > high || cube(high + 1) > N) // Adjust invariant for high
        invariant (forall x :: (cube(x) <= N < cube(x + 1)) ==> low <= x)
        invariant (forall x :: (cube(x) <= N < cube(x + 1)) ==> x <= high)
    {
        var mid := low + (high - low) / 2;

        if cube(mid) <= N
        {
            if mid == high || cube(mid + 1) > N
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