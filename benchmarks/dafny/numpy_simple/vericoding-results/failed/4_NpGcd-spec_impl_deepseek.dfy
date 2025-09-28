// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures a % gcd(a, b) == 0
  ensures if b > 0 then b % gcd(a, b) == 0 else true
  ensures forall d :: d > 0 && a % d == 0 && (b > 0 ==> b % d == 0) ==> d <= gcd(a, b)
  decreases b
{
  if b == 0 then
    a
  else
    gcd(b, a % b)
}

/* helper modified by LLM (iteration 5): Fixed preconditions to handle b=0 case */
lemma gcd_positive_properties(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
{
}

lemma gcd_mod_properties(a: int, b: int, d: int)
  requires a > 0 && b >= 0 && d > 0
  requires a % d == 0 && (b > 0 ==> b % d == 0)
  ensures gcd(a, b) % d == 0
{
}

lemma gcd_commutative(a: int, b: int)
  requires a > 0 && b >= 0
  ensures gcd(a, b) == if b > 0 then gcd(b, a) else a
{
}

lemma gcd_mod_lemma(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a % b)
  decreases b
{
  if b != 0 {
    gcd_mod_lemma(b, a % b);
  }
}
// </vc-helpers>

// <vc-spec>
method GcdInt(a: int, b: int) returns (result: int)
    ensures
        result > 0 &&
        a % result == 0 &&
        b % result == 0 &&
        (forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed handling of non-positive inputs and while loop */
  if a <= 0 || b <= 0 {
    result := 1;
    return;
  }
  
  var x := a;
  var y := b;
  
  while y != 0
    decreases y
    invariant x > 0 && y >= 0
    invariant gcd(x, y) == gcd(a, b)
  {
    var remainder := x % y;
    x := y;
    y := remainder;
  }
  result := x;
}
// </vc-code>
