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
lemma lemma_gcd_property(a: int, b: int)
  requires b != 0
  ensures forall d: int :: d > 0 ==> (divides(d, a) && divides(d, b) <==> divides(d, b) && divides(d, a % b))
{
}
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
  if a == 0 && b == 0 {
    result := 0;
  } else {
    var x := abs(a);
    var y := abs(b);

    ghost var A := x;
    ghost var B := y;

    while y != 0
      invariant x >= 0 && y >= 0
      invariant forall d: int :: d > 0 ==> (divides(d, x) && divides(d, y) <==> divides(d, A) && divides(d, B))
      decreases y
    {
      lemma_gcd_property(x, y);
      x, y := y, x % y;
    }
    result := x;
  }
}
// </vc-code>
