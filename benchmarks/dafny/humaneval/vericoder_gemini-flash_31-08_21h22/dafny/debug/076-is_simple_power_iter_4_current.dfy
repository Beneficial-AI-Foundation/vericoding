function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}

// <vc-helpers>
function is_power(base: nat, exp: nat, value: nat): bool
  decreases exp
{
  if exp == 0 then
    value == 1
  else if base == 0 && exp > 0 then
    value == 0
  else if base == 1 then
    value == 1
  else if value % base != 0 then
    false
  else
    is_power(base, exp - 1, value / base)
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
  if n < 0 {
    return false;
  }
  if x == 1 {
    return n == 1;
  }
  if n == 0 {
    return false;
  }

  var y: nat := 0;
  var current_power: int := 1; // Change to int to match n's type for comparison

  while current_power < n
    invariant current_power == power(x, y)
    invariant x > 0
    invariant current_power > 0
    invariant current_power >= 1
    invariant current_power <= n || n <= power(x, y-1) // If current_power > n, then a previous power was <= n and next one exceeded n.
    invariant y < n // y can't exceed n as current_power grows exponentially.

  {
    if x == 0 {
      ans := false;
      return;
    }

    if current_power > n / x {
      break;
    }
    current_power := current_power * x;
    y := y + 1;
  }

  ans := current_power == n;
}
// </vc-code>

