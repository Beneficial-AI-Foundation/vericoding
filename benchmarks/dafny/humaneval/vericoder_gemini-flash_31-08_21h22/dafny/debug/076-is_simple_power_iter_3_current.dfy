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
    return n == 1; // n = power(1, y) implies n = 1
  }
  if n == 0 {
    return false; // power(x,y) for x > 0 and y >= 0 is always >= 1
  }

  var y: nat := 0;
  var current_power: nat := 1;

  while current_power < n
    invariant current_power == power(x, y)
    invariant x > 0
    invariant current_power > 0
    invariant current_power >= 1
    invariant y <= n // y can't exceed n as current_power grows exponentially, n is an upper bound on y.
                     // A tighter bound ensures termination without being overly complex:
                     // if x >= 2, current_power = x^y grows very fast. If x = 1, handled specifically.
  {
    if x == 0 { // Precondition already states x > 0.
      ans := false;
      return;
    }
    // Check for potential overflow before multiplication: current_power * x
    // If current_power > max_nat / x, then current_power * x would overflow
    // Since current_power and x are nat, and current_power < n, n is an int that could be very large
    // We already know current_power < n. If current_power * x overflows, n could not be that power.
    // However, Dafny's `nat` type implicitly handles this by checking for `current_power * x` to be a nat.
    // The main concern is `current_power * x` becoming greater than `n` and `current_power * x` potentially overflowing `nat` type.
    if current_power > n / x { // Avoid overflow for comparison with n, as n is int.
                               // If current_power * x would exceed n,
                               // and current_power is already close to n.
                               // current_power*x will then be > n, so the loop will stop.
                               // This guard prevents `current_power * x` from exceeding `n` and potentially overflowing if n was max_nat,
                               // even though power returns nat, which does not overflow.
                               // Here, current_power * x can't exceed n to become 'n' itself if it is already > n/x.
      break; // current_power * x would be >= n, and potentially greater, so it would break the loop anyway.
             // We can exit and do the final check.
    }
    current_power := current_power * x;
    y := y + 1;
  }

  ans := current_power == n;
}
// </vc-code>

