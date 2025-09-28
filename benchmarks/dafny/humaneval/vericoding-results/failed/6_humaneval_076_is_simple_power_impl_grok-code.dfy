// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
function is_simple_power_func(x: nat, n: int) : (res: bool)
  requires x > 0
  ensures res <==> exists y : nat :: n == power(x, y)
  decreases if n >= 0 then n else 0
  /* helper modified by LLM (iteration 5): Fix syntax to use then/else and correct logic in else branches */
{
  if n <= 0 then
    false
  else if x == 1 then
    n == 1
  else
    var remainder := n % x;
    if remainder == 0 then
      is_simple_power_func(x, n / x)
    else
      false
}
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Call the helper function to set the result */
  ans := is_simple_power_func(x, n);
}
// </vc-code>
