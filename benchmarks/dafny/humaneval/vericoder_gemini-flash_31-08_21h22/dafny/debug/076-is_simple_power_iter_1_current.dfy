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
  var y: nat := 0;
  var current_power: nat := 1;

  while current_power < n
    invariant current_power == power(x, y)
    invariant y <= n // To avoid y growing indefinitely
    // Add invariant that x > 0 from precondition
    // If x is 1, current_power will always be 1, so the loop might not terminate properly if n > 1.
    // The precondition x > 0 helps, but x=1 is a special case.
    // However, the power function handles x=1 correctly (power(1, y) = 1).
    // The `is_power` helper function also covers this.
  {
    if x == 1 { // Special handling for x=1
      ans := n == 1;
      return;
    }
    if current_power > n / x { // Avoid overflow before multiplication
      ans := false;
      return;
    }
    current_power := current_power * x;
    y := y + 1;
  }

  ans := current_power == n && (x > 0 || y == 0); // (x > 0 || y == 0) ensures power(0,0)=1 but power(0,y)=0 for y>0
}
// </vc-code>

