// <vc-preamble>
function power(x: nat, y: nat): nat {
    if y == 0 then 1 else x * power(x, y-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Minor update to prevent compilation or verification issues by ensuring the lemma is correctly defined. */
lemma PowerNext(x: nat, y: nat, p: nat)
requires x > 0 && p == power(x, y)
ensures (p * x) == power(x, y+1)
{ }
// </vc-helpers>

// <vc-spec>
method is_simple_power(x: nat, n: int) returns (ans : bool)

    requires x > 0

    ensures ans <==> exists y :: n == power(x, y)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added case for x==1 to ensure termination when x==1, added assert for lemma precondition to assist verification, added decreases clause for loop termination, and adjusted checks for n<=0. */
  ans := false;
  if n <= 0 {
    // ans remains false
  } else if x == 1 {
    ans := n == 1;
  } else {
    var y: nat := 0;
    var p: nat := 1;
    assert p == power(x, y);
    while (p as int) < n
      decreases n - (p as int)
    {
      y := y + 1;
      assert p == power(x, y-1);
      PowerNext(x, y-1, p);
      p := p * x;
      assert p == power(x, y);
      if (p as int) == n {
        ans := true;
        return;
      }
    }
    ans := (p as int) == n;
  }
}
// </vc-code>
