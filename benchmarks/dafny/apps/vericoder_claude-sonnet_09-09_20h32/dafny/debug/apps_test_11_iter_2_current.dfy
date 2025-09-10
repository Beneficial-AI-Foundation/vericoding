predicate ValidInput(n: int, a: int, b: int, p: int, q: int) {
  n > 0 && a > 0 && b > 0 && p > 0 && q > 0
}

function gcd(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures gcd(a, b) > 0
  decreases b
{
  if b == 0 then a else gcd(b, a % b)
}

// <vc-helpers>
lemma DivisionProperties(x: int, y: int)
  requires y > 0
  ensures x / y >= 0 <==> x >= 0
  ensures x >= 0 && y >= 1 ==> x / y <= x
{
  if x >= 0 && y >= 1 {
    if y == 1 {
      assert x / y == x;
    } else {
      assert y > 1;
      assert x / y <= x;
    }
  }
}

lemma GcdProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) <= a && gcd(a, b) <= b
  ensures gcd(a, b) > 0
  decreases if a < b then b else a
{
  if b == 0 {
    assert gcd(a, b) == a;
    assert a <= a && a <= b;
  } else if a >= b {
    assert gcd(a, b) == gcd(b, a % b);
    assert a % b >= 0 && a % b < b;
    if a % b == 0 {
      assert gcd(a, b) == b;
      assert b <= a && b <= b;
    } else {
      GcdProperties(b, a % b);
      assert gcd(b, a % b) <= b && gcd(b, a % b) <= a % b;
      assert a % b < b <= a;
      assert gcd(a, b) <= b <= a;
    }
  } else {
    assert a < b;
    assert gcd(a, b) == gcd(b, a % b);
    assert a % b == a;
    assert gcd(a, b) == gcd(b, a);
    GcdProperties(b, a);
  }
}

lemma MultiplicationNonNegative(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures x * y >= 0
{
}

lemma LcmPositive(a: int, b: int)
  requires a > 0 && b > 0
  ensures (a * b) / gcd(a, b) > 0
{
  GcdProperties(a, b);
  assert gcd(a, b) > 0;
  assert gcd(a, b) <= a && gcd(a, b) <= b;
  assert a * b > 0;
  assert (a * b) / gcd(a, b) > 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var g := gcd(a, b);
  GcdProperties(a, b);
  LcmPositive(a, b);
  var lcm := (a * b) / g;
  
  var countA := n / a;
  var countB := n / b;
  var countLcm := n / lcm;
  
  result := countA * p + countB * q - countLcm * (p + q);
  
  if result < 0 {
    result := 0;
  }
}
// </vc-code>

