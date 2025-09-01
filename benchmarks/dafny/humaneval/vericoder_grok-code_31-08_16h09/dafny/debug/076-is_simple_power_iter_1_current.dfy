function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
// </vc-helpers>
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
  if x == 1 {
    return n == 1;
  }
  var acc := 1;
  var y := 0;
  while acc != n && acc < n
    invariant 0 < x
    invariant y == 0 ==> acc == 1
  {
    acc := acc * x;
    y := y + 1;
  }
  return acc == n;
}
// </vc-code>
// </vc-code>

