// recursive version should be more promising

// <vc-helpers>
function gcd(a: nat, b: nat): nat
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a < b then gcd(a, b - a)
  else gcd(a - b, b)
}

lemma gcd_properties(a: nat, b: nat)
  ensures gcd(a, b) == gcd(b, a)
  ensures a > 0 ==> gcd(a, b) > 0
  ensures b > 0 ==> gcd(a, b) > 0
  ensures gcd(a, b) <= a || a == 0
  ensures gcd(a, b) <= b || b == 0
{
}

lemma gcd_divides(a: nat, b: nat)
  requires a > 0 || b > 0
  ensures gcd(a, b) > 0
  ensures a == 0 || a % gcd(a, b) == 0
  ensures b == 0 || b % gcd(a, b) == 0
{
  if a == 0 {
  } else if b == 0 {
  } else if a < b {
    gcd_divides(a, b - a);
  } else {
    gcd_divides(a - b, b);
  }
}

function abs(x: int): nat
{
  if x >= 0 then x else -x
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def greatest_common_divisor(a: int, b: int) -> int
Return a greatest common divisor of two integers a and b
*/
// </vc-description>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (result: int)
  requires a != 0 || b != 0
  ensures result > 0
  ensures a % result == 0
  ensures b % result == 0
  ensures result == gcd(abs(a), abs(b))
// </vc-spec>
// <vc-code>
{
  var abs_a := abs(a);
  var abs_b := abs(b);
  gcd_divides(abs_a, abs_b);
  result := gcd(abs_a, abs_b);
}
// </vc-code>
