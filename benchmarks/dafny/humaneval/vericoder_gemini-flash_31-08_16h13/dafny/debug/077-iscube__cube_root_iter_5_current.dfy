

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
    var low: nat := 0;
    var high: nat := N;
    var r_val: nat := 0;

    while low <= high
        invariant 0 <= low
        invariant high <= N
        invariant low <= high + 1
        invariant cube_nat(low) <= N || low == 0 // Corrected invariant for cube_nat(low) <= N
        invariant high == N || cube_nat(high) > N || low > high || cube_nat(high + 1) > N // Corrected invariant for high
        invariant (forall x: nat :: (cube_nat(x) <= N < cube_nat(x + 1)) ==> low <= x)
        invariant (forall x: nat :: (cube_nat(x) <= N < cube_nat(x + 1)) ==> x <= high + 1)
        invariant (exists k: nat :: low <= k <= high+1 && cube_nat(k) <= N < cube_nat(k + 1)) ==> low <= high + 1 // Added invariant for search space
    {
        var mid := low + (high - low) / 2;

        if cube_nat(mid) <= N
        {
            if mid == high || cube_nat(mid + 1) > N
            {
                r_val := mid;
                break; // Found the cube root, exit loop
            }
            else
            {
                low := mid + 1;
            }
        }
        else
        {
            if mid == 0 { // Avoid mid-1 when mid is 0
                high := 0;
            } else {
                high := mid - 1;
            }
        }
    }
    r := r_val;
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