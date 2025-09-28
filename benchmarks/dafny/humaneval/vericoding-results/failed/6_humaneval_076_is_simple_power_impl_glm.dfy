// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added invariant for future powers to prove postcondition */
  if n <= 0 {
    ans := false;
  } else if x == 1 {
    ans := n == 1;
  } else {
    var current := 1;
    var y := 0;
    while current < n
      invariant y >= 0
      invariant current == power(x, y)
      invariant forall y' :: 0 <= y' < y ==> power(x, y') < n
      invariant forall y' :: y' >= y ==> power(x, y') >= current
      decreases n - current
    {
      y := y + 1;
      current := current * x;
    }
    ans := current == n;
  }
}
// </vc-code>
