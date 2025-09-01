method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function cube_nat(n: nat): nat { n * n * n }
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
  var low: nat := 0;
  var high: nat := n;

  while low <= high
    invariant 0 <= low <= n + 1
    invariant 0 <= high <= n
    invariant forall k: nat :: (k < low || k > high) ==> (cube_nat(k) != n)
  {
    var mid: nat := (low + high) / 2;
    if mid * mid * mid == n
    {
      r := true;
      return;
    }
    else if mid * mid * mid > n
    {
      if mid == 0 {
          // If mid is 0, then mid*mid*mid is 0, which cannot be > n unless n is very small.
          // In this case, if n is not 0, then the cube root cannot be found below 0.
          // And if n is 0, then mid*mid*mid == n, and it would be caught by the first `if` statement.
          // So if we reach here and mid is 0 and mid*mid*mid > n, it's impossible.
          // To satisfy the loop invariant and termination, we can break from the loop.
          high := mid - 1; // This will make high negative and terminate the loop
      } else {
        high := mid - 1;
      }
    }
    else // mid * mid * mid < n
    {
      low := mid + 1;
    }
  }

  r := false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end