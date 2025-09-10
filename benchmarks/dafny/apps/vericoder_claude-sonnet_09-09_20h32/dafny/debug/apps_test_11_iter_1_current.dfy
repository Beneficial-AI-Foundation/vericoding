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
  ensures x >= 0 ==> x / y <= x
{
}

lemma GcdProperties(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) <= a && gcd(a, b) <= b
  ensures gcd(a, b) > 0
{
}

lemma MultiplicationNonNegative(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures x * y >= 0
{
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

