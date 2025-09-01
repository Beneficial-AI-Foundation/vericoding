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

  if n == 0 {
    r := true; // cube_nat(0) == 0
    return;
  }
  
  while low <= high
    invariant 0 <= low <= n + 1
    invariant 0 <= high <= n
    invariant forall k: nat :: (k < low || k > high) ==> (cube_nat(k) != n)
    decreases high - low
  {
    var mid: nat := (low + high) / 2;
    if mid > n { // Prevent overflow and out-of-bounds access if mid becomes very large
      high := mid - 1;
      continue;
    }
    
    var mid_cubed: nat := cube_nat(mid);

    if mid_cubed == n
    {
      r := true;
      return;
    }
    else if mid_cubed > n
    {
      if mid == 0 { // Should not happen if n > 0
          high := 0; // Ensures termination
      } else {
        high := mid - 1;
      }
    }
    else // mid_cubed < n
    {
      low := mid + 1;
    }
  }

  r := false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end