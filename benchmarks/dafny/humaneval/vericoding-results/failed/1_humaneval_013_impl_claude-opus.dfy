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
/* helper modified by LLM (iteration 5): Removed recursive lemmas to avoid timeouts, using iterative gcd */
function gcd(a: nat, b: nat): nat
  decreases b
{
  if b == 0 then a
  else gcd(b, a % b)
}

ghost function gcdProp(a: nat, b: nat): (nat, bool, bool)
  ensures gcdProp(a, b).0 == gcd(a, b)
  ensures gcdProp(a, b).1 == divides(gcd(a, b), a)
  ensures gcdProp(a, b).2 == divides(gcd(a, b), b)
  decreases b
{
  if b == 0 then
    (a, true, true)
  else
    var (g, _, _) := gcdProp(b, a % b);
    (g, true, true)
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
/* code modified by LLM (iteration 5): Simplified to avoid lemma timeouts */
{
  if a == 0 && b == 0 {
    result := 0;
  } else {
    var aa := abs(a);
    var bb := abs(b);
    
    var aa' := aa;
    var bb' := bb;
    while bb' > 0
      invariant 0 <= bb' <= bb
      invariant gcd(aa', bb') == gcd(aa, bb)
      decreases bb'
    {
      var temp := bb';
      bb' := aa' % bb';
      aa' := temp;
    }
    result := aa';
    
    assert result == gcd(aa, bb);
    assert result > 0;
  }
}
// </vc-code>
