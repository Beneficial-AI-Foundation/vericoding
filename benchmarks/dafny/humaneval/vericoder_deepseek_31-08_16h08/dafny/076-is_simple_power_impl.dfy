function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma power_monotonic(x: nat, y1: nat, y2: nat)
  requires x > 0
  requires y1 <= y2
  ensures power(x, y1) <= power(x, y2)
{
  if y1 == y2 {
  } else {
    power_monotonic(x, y1, y2-1);
    assert power(x, y2-1) <= power(x, y2-1);
    assert x * power(x, y2-1) >= power(x, y2-1);
  }
}

lemma power_positive(x: nat, y: nat)
  requires x > 0
  ensures power(x, y) > 0
{
  if y == 0 {
  } else {
    power_positive(x, y-1);
  }
}

lemma power_ge_one(x: nat, y: nat)
  requires x > 0
  ensures power(x, y) >= 1
{
  if y == 0 {
  } else {
    power_positive(x, y-1);
  }
}

lemma power_strictly_increasing(x: nat, y: nat)
  requires x > 1
  ensures power(x, y) < power(x, y+1)
{
  power_positive(x, y);
  assert power(x, y+1) == x * power(x, y);
  assert x * power(x, y) > 1 * power(x, y);
}

lemma power_zero_case(x: nat, y: nat)
  requires x == 0
  ensures power(x, y) == 0 || power(x, y) == 1
{
  if y == 0 {
  } else {
  }
}

lemma power_of_one(y: nat)
  ensures power(1, y) == 1
{
  if y == 0 {
  } else {
    power_of_one(y-1);
  }
}

lemma power_never_equals_n(x: nat, n: int, y: nat)
  requires x > 1
  requires n >= 1
  requires power(x, y) > n
  ensures forall y' :: y' >= y ==> power(x, y') != n
{
}

lemma power_always_increasing(x: nat, y: nat)
  requires x > 1
  ensures power(x, y) < power(x, y+1)
{
  power_positive(x, y);
  assert power(x, y+1) == x * power(x, y);
  assert x > 1;
  assert power(x, y+1) > power(x, y);
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)
    // pre-conditions-start
    requires x > 0
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists y :: n == power(x, y)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if n < 1 {
    ans := n == 1;
    return;
  }
  
  var y: nat := 0;
  var p: nat := 1;
  
  while p <= n
    invariant p == power(x, y)
    invariant forall y' :: 0 <= y' < y ==> power(x, y') != n
    decreases if x <= 1 then 0 else n - p
  {
    if p == n {
      ans := true;
      return;
    }
    
    if x == 1 {
      ans := false;
      return;
    }
    
    y := y + 1;
    p := p * x;
  }
  
  ans := false;
}
// </vc-code>

