// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause for termination */
function gcd_positive(a: int, b: int): int
    requires a >= 0 && b >= 0
    requires a != 0 || b != 0
    ensures gcd_positive(a, b) != 0
decreases b
{
    if b == 0 then a
    else gcd_positive(b, a % b)
}
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)

    requires a != 0 || b != 0

    ensures gcd != 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): no change */
{
  var a_abs := if a < 0 then -a else a;
  var b_abs := if b < 0 then -b else b;

  gcd := gcd_positive(a_abs, b_abs);
}
// </vc-code>
