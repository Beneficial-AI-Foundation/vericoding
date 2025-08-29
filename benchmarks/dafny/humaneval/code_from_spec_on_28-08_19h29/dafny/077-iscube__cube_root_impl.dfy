// <vc-helpers>
function cube_root_helper(n: int): int 
{
  n * n * n
}

lemma CubeMonotonic(a: nat, b: nat)
  requires a <= b
  ensures cube_root_helper(a) <= cube_root_helper(b)
{
  if a == b {
    assert cube_root_helper(a) == cube_root_helper(b);
  } else {
    var diff := b - a;
    assert diff > 0;
    assert cube_root_helper(b) == cube_root_helper(a + diff);
    assert cube_root_helper(a + diff) == a*a*a + 3*a*a*diff + 3*a*diff*diff + diff*diff*diff;
    assert 3*a*a*diff + 3*a*diff*diff + diff*diff*diff > 0;
    assert cube_root_helper(a + diff) > cube_root_helper(a);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method cube_root(N: nat) returns (r: nat)
Find the integer cube root. Ensures: the result r is the largest integer such that r³ ≤ N < (r+1)³; the result is at most N.
*/
// </vc-description>

// <vc-spec>
method cube_root(N: nat) returns (r: nat)
  requires N >= 0
  ensures r * r * r <= N < (r + 1) * (r + 1) * (r + 1)
  ensures r <= N
// </vc-spec>
// <vc-code>
{
  if N == 0 {
    return 0;
  }

  var low: nat := 0;
  var high: nat := N;

  while low < high
    invariant low <= high
    invariant low * low * low <= N
    invariant high == N || (high + 1) * (high + 1) * (high + 1) > N
    decreases high - low
  {
    var mid: nat := (low + high + 1) / 2;
    var mid_cube := mid * mid * mid;

    if mid_cube <= N {
      low := mid;
    } else {
      high := mid - 1;
    }
  }

  return low;
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