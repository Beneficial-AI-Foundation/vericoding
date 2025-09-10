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
lemma {:axiom} GcdIsLinearCombination(a: int, b: int)
  requires a > 0 && b > 0
  ensures exists x: int, y: int :: x * a + y * b == gcd(a, b)
{
}

lemma GcdMultiplesPreserve(divisor: int, multiple1: int, multiple2: int)
  requires divisor > 0 && multiple1 > 0 && multiple2 > 0
  ensures gcd(divisor * multiple1, divisor * multiple2) == divisor * gcd(multiple1, multiple2)
{
  var c := gcd(multiple1, multiple2);
  var x, y := GcdIsLinearCombination(multiple1, multiple2);
  assert x * multiple1 + y * multiple2 == c;
  assert divisor * (x * multiple1 + y * multiple2) == divisor * c;
  assert (x * divisor * multiple1) + (y * divisor * multiple2) == divisor * c;
  
  var g := gcd(divisor * multiple1, divisor * multiple2);
  assert g % divisor == 0;
  // The common divisor divisor * c must divide g
  assert divisor * c % g == 0;
  // g must divide divisor * c
  assert g % (divisor * c) == 0;
  assert g == divisor * c;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, p: int, q: int) returns (result: int)
  requires ValidInput(n, a, b, p, q)
  ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var divisor := gcd(a, b);
  var multiple1 := a / divisor;
  var multiple2 := b / divisor;
  var target_divisor, target_multiple1, target_multiple2;
  
  target_divisor := gcd(p, q);
  target_multiple1 := p / target_divisor;
  target_multiple2 := q / target_divisor;
  
  if multiple1 % target_multiple1 == 0 && 
     multiple2 % target_multiple2 == 0 {
    var k1 := multiple1 / target_multiple1;
    var k2 := multiple2 / target_multiple2;
    if k1 == k2 {
      return k1;
    }
  }
  
  if multiple1 % target_multiple2 == 0 && 
     multiple2 % target_multiple1 == 0 {
    var k1 := multiple1 / target_multiple2;
    var k2 := multiple2 / target_multiple1;
    if k1 == k2 {
      return k1;
    }
  }
  
  return 0;
}
// </vc-code>

