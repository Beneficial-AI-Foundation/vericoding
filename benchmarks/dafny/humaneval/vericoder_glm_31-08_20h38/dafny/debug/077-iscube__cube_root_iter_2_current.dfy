

// <vc-helpers>

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
  var low := 0;
  var high := N;
  while low < high
    invariant 0 <= low <= high <= N
    invariant cube(low) <= N
    invariant cube(high + 1) > N
    decreases high - low
  {
    var mid := (low + high) / 2;
    if cube(mid + 1) <= N {
      low := mid + 1;
    } else {
      high := mid;
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