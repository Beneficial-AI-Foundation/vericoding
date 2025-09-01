// recursive version should be more promising

// <vc-helpers>
lemma GcdPositive(a: int, b: int)
  requires a != 0 || b != 0
  ensures gcd(a, b) != 0
{
}

function gcd(a: int, b: int): int
  requires a != 0 || b != 0
{
  if a == 0 then b
  else if b == 0 then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}
// </vc-helpers>

// <vc-spec>
method greatest_common_divisor(a: int, b: int) returns (gcd: int)
    // pre-conditions-start
    requires a != 0 || b != 0
    // pre-conditions-end
    // post-conditions-start
    ensures gcd != 0
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if a == 0 {
    gcd := b;
  } else if b == 0 {
    gcd := a;
  } else if a > b {
    gcd := greatest_common_divisor(a - b, b);
  } else {
    gcd := greatest_common_divisor(a, b - a);
  }
}
// </vc-code>

