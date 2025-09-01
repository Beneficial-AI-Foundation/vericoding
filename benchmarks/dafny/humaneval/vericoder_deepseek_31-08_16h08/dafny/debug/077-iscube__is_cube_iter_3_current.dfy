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
  if a < b {
    var i := a;
    while i < b
      invariant a <= i <= b
      invariant cube(a) <= cube(i)
      decreases b - i
    {
      assert cube(i) <= cube(i + 1) by {
        calc {
          cube(i + 1);
          ==
          (i + 1) * (i + 1) * (i + 1);
          ==
          i*i*i + 3*i*i + 3*i + 1;
          >=
          i*i*i;
          ==
          cube(i);
        }
      }
      i := i + 1;
    }
  }
}

lemma cube_strictly_increasing(a: nat, b: nat)
  requires a < b
  ensures cube(a) < cube(b)
{
  cube_monotonic(a, b);
  if b > a + 1 {
    cube_strictly_increasing(a, b - 1);
  }
}

lemma cube_root_exists(n: nat)
  ensures exists r: nat :: cube(r) <= n < cube(r + 1)
{
  var r: nat := 0;
  while cube(r + 1) <= n
    invariant cube(r) <= n
    invariant r <= n
    decreases n - r
  {
    r := r + 1;
  }
}

lemma cube_properties(n: nat)
  ensures forall r: nat :: 0 <= r <= n ==> cube(r) <= cube(n)
{
}

lemma cube_nonnegative(n: nat)
  ensures cube(n) >= 0
{
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
  if n == 0 {
    r := true;
    return;
  }
  
  var low: nat := 0;
  var high: nat := n;
  
  while low <= high
    invariant 0 <= low <= high <= n
    invariant cube(low) <= n <= cube(high)
    decreases high - low
  {
    var mid: nat := (low + high) / 2;
    var mid_cubed: nat := cube(mid);
    
    if mid_cubed < n {
      low := mid + 1;
    } else if mid_cubed > n {
      high := mid - 1;
    } else {
      r := true;
      return;
    }
  }
  
  r := false;
}
// </vc-code>

function cube(n: int): int { n * n * n }
// pure-end