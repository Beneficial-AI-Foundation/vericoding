function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
lemma PowerProperties(x: nat, y: nat)
  ensures power(x, y) >= 1
  ensures y > 0 ==> power(x, y) >= x
{
  if y == 0 {
    assert power(x, y) == 1;
  } else {
    PowerProperties(x, y-1);
    assert power(x, y) == x * power(x, y-1);
    assert power(x, y-1) >= 1;
    assert x >= 0;
    assert power(x, y) >= x * 1;
  }
}

lemma PowerMonotonic(x: nat, y1: nat, y2: nat)
  requires x > 1
  requires y1 < y2
  ensures power(x, y1) < power(x, y2)
  decreases y2 - y1
{
  if y1 + 1 == y2 {
    assert power(x, y2) == x * power(x, y1);
    assert x > 1;
    assert power(x, y1) >= 1;
    assert x * power(x, y1) > power(x, y1);
  } else {
    PowerMonotonic(x, y1, y2 - 1);
    PowerMonotonic(x, y2 - 1, y2);
    assert power(x, y1) < power(x, y2 - 1);
    assert power(x, y2 - 1) < power(x, y2);
  }
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
method IsSimplePower(x: nat, n: int) returns (ans: bool)
  requires x > 0
  ensures ans <==> exists y :: n == power(x, y)
{
  if n <= 0 {
    return false;
  }
  
  if x == 1 {
    return n == 1;
  }
  
  var current := 1;
  var y := 0;
  
  while current < n
    invariant current == power(x, y)
    invariant current > 0
    invariant current <= n
    invariant x > 1
  {
    if current > n / x {
      return false;
    }
    current := current * x;
    y := y + 1;
  }
  
  ans := current == n;
  if ans {
    assert n == power(x, y);
    assert exists y' :: n == power(x, y');
  } else {
    if x > 1 {
      if current > n {
        PowerMonotonic(x, y - 1, y);
        assert power(x, y) > n;
        assert forall y' :: y' >= y ==> power(x, y') >= power(x, y) > n;
        assert forall y' :: y' < y ==> power(x, y') <= power(x, y - 1) < n;
        assert forall y' :: power(x, y') != n;
      } else {
        assert current == n;
      }
    }
  }
  return ans;
}
// </vc-code>
