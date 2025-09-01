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
    assert cube(b - 1) < cube(b) by {
      calc {
        cube(b);
        ==
        b * b * b;
        >
        (b - 1) * (b - 1) * (b - 1);
        ==
        cube(b - 1);
      }
    }
  } else {
    assert cube(a) < cube(a + 1) by {
      calc {
        cube(a + 1);
        ==
        (a + 1) * (a + 1) * (a + 1);
        ==
        a*a*a + 3*a*a + 3*a + 1;
        >
        a*a*a;
        ==
        cube(a);
      }
    }
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

lemma cube_invariant_maintained(low: nat, high: nat, n: nat, new_val: nat, is_low: bool)
  requires 0 <= low <= high <= n
  requires cube(low) <= n <= cube(high)
  requires is_low ==> (new_val == low + 1 && cube(low) < n)
  requires !is_low ==> (new_val == high - 1 && n < cube(high))
  ensures 0 <= (if is_low then new_val else low) <= (if is_low then high else new_val) <= n
  ensures cube(if is_low then new_val else low) <= n <= cube(if is_low then high else new_val)
{
  if is_low {
    assert new_val <= high;
    assert cube(new_val) <= n by {
      if low + 1 <= high {
        cube_monotonic(low + 1, high);
        assert cube(low + 1) <= cube(high) <= n;
      }
    }
    assert n <= cube(high);
  } else {
    assert low <= new_val;
    assert cube(low) <= n;
    assert n <= cube(new_val) by {
      if high - 1 >= low {
        cube_monotonic(low, high - 1);
        assert n < cube(high) <= cube(high - 1);
      }
    }
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
      cube_invariant_maintained(low, high, n, mid + 1, true);
      low := mid + 1;
    } else if mid_cubed > n {
      cube_invariant_maintained(low, high, n, mid - 1, false);
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