function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>

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
  if n <= 0 {
      return false;
  }
  if n == 1 {
      return true;
  }
  if x == 1 {
      return false;
  }
  var current := n;
  while current > 1
    invariant current > 0
    invariant n % current == 0
    decreases current
  {
      if current % x != 0 {
          return false;
      }
      var k := current / x;
      var m := n / current;
      assert n == current * m;
      assert current == x * k;
      assert n == x * k * m;
      assert n % k == 0;
      current := current / x;
  }
  return true;
}
// </vc-code>

