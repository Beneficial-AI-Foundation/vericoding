// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed redundant helper. */
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Simplified the logic and corrected the return condition for handling the base cases and the general case for checking if 'n' is a power of 'x'. The redundant 'assume false' has been removed and the code now directly implements the power check logic. */
{
  if n < 0 {
    return false;
  }
  if n == 0 {
    return false;
  }
  if n == 1 {
    return true;
  }
  if x == 1 {
    return n == 1;
  }

  var current_n := n;

  while current_n > 1
    invariant current_n > 0
    invariant current_n % x == 0 || (current_n == n && n % x != 0) // if current_n is not divisible by x, it must be the original n which was not a power of x
    decreases current_n
  {
    if current_n % x != 0 {
      return false;
    }
    current_n := current_n / x;
  }
  return current_n == 1;
}
// </vc-code>
