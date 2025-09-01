method cube_root(N: nat) returns (r: nat)
  // post-conditions-start
  ensures cube(r) <= N < cube(r + 1)
  ensures r <= N
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma cube_monotonic(a: nat, b: nat)
  requires a <= b
  ensures cube(a) <= cube(b)
{
}

lemma cube_strictly_increasing(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
}

lemma cube_root_exists(n: nat)
  ensures exists r: nat :: cube(r) <= n < cube(r + 1)
{
  var r := 0;
  while cube(r + 1) <= n
    invariant cube(r) <= n
    invariant r <= n
    decreases n - r
  {
    r := r + 1;
  }
}
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
  
  while low < high
    invariant 0 <= low <= high <= n
    invariant cube(low) <= n < cube(high + 1)
    decreases high - low
  {
    var mid: nat := (low + high) / 2;
    var mid_cubed: int := cube(mid);
    
    if mid_cubed <= n {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  r := cube(low - 1) == n;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end