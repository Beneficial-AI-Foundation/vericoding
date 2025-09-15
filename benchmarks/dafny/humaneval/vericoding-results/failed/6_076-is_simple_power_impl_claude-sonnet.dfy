// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed calc step justification and assertion proof */
lemma power_monotonic(x: nat, y1: nat, y2: nat)
  requires x > 1
  requires y1 < y2
  ensures power(x, y1) < power(x, y2)
  decreases y2 - y1
{
  if y2 == y1 + 1 {
    calc {
      power(x, y2);
      == power(x, y1 + 1);
      == x * power(x, y1);
      >= x * power(x, y1);
    }
    assert x >= 2;
    assert x * power(x, y1) >= 2 * power(x, y1);
    assert 2 * power(x, y1) > power(x, y1);
  } else {
    power_monotonic(x, y1, y2 - 1);
    power_monotonic(x, y2 - 1, y2);
  }
}

lemma power_grows(x: nat, y: nat)
  requires x > 1
  requires y > 0
  ensures power(x, y) >= y
{
  if y == 1 {
    assert power(x, 1) == x >= 1;
  } else {
    power_grows(x, y - 1);
    calc {
      power(x, y);
      == x * power(x, y - 1);
      >= x * (y - 1);
      >= 2 * (y - 1);
      == 2 * y - 2;
      >= y;
    }
  }
}

lemma power_bound(x: nat, y: nat, n: int)
  requires x > 1
  requires power(x, y) <= n
  ensures y <= n
{
  if y > 0 {
    power_grows(x, y);
    assert power(x, y) >= y;
    if y > n {
      assert power(x, y) >= y > n;
      assert false;
    }
  }
}

lemma power_one_base(y: nat)
  ensures power(1, y) == 1
{
  if y == 0 {
    assert power(1, 0) == 1;
  } else {
    power_one_base(y - 1);
    calc {
      power(1, y);
      == 1 * power(1, y - 1);
      == 1 * 1;
      == 1;
    }
  }
}

lemma power_one_all()
  ensures forall y :: power(1, y) == 1
{
  forall y {
    power_one_base(y);
  }
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed assertion proof and logic */
{
  if n <= 0 {
    if n == 1 {
      ans := true;
      assert power(x, 0) == 1;
    } else {
      ans := false;
      assert forall y :: power(x, y) >= 1;
    }
    return;
  }
  
  if x == 1 {
    ans := n == 1;
    if n == 1 {
      assert power(1, 0) == 1;
    } else {
      power_one_all();
    }
    return;
  }
  
  var current_power := 1;
  var y := 0;
  
  while current_power < n
    invariant current_power == power(x, y)
    invariant y <= n
    invariant current_power <= n
    invariant forall z :: 0 <= z < y ==> power(x, z) < n
  {
    if current_power > n / x {
      ans := false;
      assert current_power * x > n;
      assert power(x, y + 1) == current_power * x > n;
      assert forall z :: power(x, z) != n;
      return;
    }
    current_power := current_power * x;
    y := y + 1;
    if current_power <= n {
      power_bound(x, y, n);
    }
  }
  
  ans := current_power == n;
  if ans {
    assert power(x, y) == n;
  } else {
    assert current_power > n;
    assert forall z :: 0 <= z <= y ==> power(x, z) != n;
    if x > 1 {
      assert forall z :: z > y ==> power(x, z) > power(x, y) > n;
    }
  }
}
// </vc-code>
