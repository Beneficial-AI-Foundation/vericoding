// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
function is_power_helper(x: nat, k: nat): (result: bool)
  requires x > 0
  ensures result <==> (exists y :: x == power(k, y))
{
  if k == 1 then
    x == 1
  else if k > x then
    false
  else
    var temp: nat := 1;
    var exp: nat := 0;
    while temp <= x
      invariant temp == power(k, exp)
      invariant temp >= 1
    {
      if temp == x then
        return true;
      if temp * k > x then
        break;
      temp := temp * k;
      exp := exp + 1;
    }
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
  /* code modified by LLM (iteration 5): Fixed variable name and logic */
  if n <= 0 then
    ans := false;
  else if n == 1 then
    ans := (x == 1);
  else
    ans := is_power_helper(n as nat, x);
}
// </vc-code>
