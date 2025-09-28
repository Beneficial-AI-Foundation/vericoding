// <vc-preamble>

function abs(x: int): nat
{
    if x >= 0 then x else -x
}

predicate divides(d: int, n: int)
{
    if d == 0 then n == 0 else n % d == 0
}
// </vc-preamble>

// <vc-helpers>
function gcd(a: nat, b: nat): nat
  ensures divides(result, a) && divides(result, b)
  ensures result == 0 <==> (a == 0 && b == 0)
  ensures forall d: nat :: d > 0 && divides(d, a) && divides(d, b) ==> d <= result
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}
/* helper modified by LLM (iteration 5): Fixed function syntax to have ensures clauses before the body */
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (result: nat)
    ensures result > 0 <==> (a != 0 || b != 0)
    ensures result == 0 <==> (a == 0 && b == 0)
    ensures divides(result, a) && divides(result, b)
    ensures forall d: int :: d > 0 && divides(d, a) && divides(d, b) ==> d <= result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implemented Euclidean algorithm using helper function */
  var a_abs := abs(a);
  var b_abs := abs(b);
  if a_abs == 0 && b_abs == 0 {
    result := 0;
  } else {
    result := gcd(a_abs, b_abs);
  }
}
// </vc-code>
