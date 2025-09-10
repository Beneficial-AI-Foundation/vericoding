predicate ValidInput(a: int, b: int, c: int, d: int) {
    a > 0 && b > 0 && c > 0 && d > 0
}

predicate IsValidFractionString(s: string, num: int, den: int) {
    num >= 0 && den > 0 && 
    gcd(num, den) == 1 &&
    s == intToString(num) + "/" + intToString(den)
}

// <vc-helpers>
function gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases a, b
{
  if a == b then
    a
  else if a > b then
    gcd(a - b, b)
  else
    gcd(a, b - a)
}

function intToString(n: int): string

lemma gcd_pos(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  decreases a, b
{
  if a == b {
  } else if a > b {
    gcd_pos(a - b, b);
  } else {
    gcd_pos(a, b - a);
  }
}

lemma gcd_div(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) > 0
  ensures a % gcd(a, b) == 0 && b % gcd(a, b) == 0
  decreases a, b
{
  if a == b {
  } else if a > b {
    gcd_div(a - b, b);
  } else {
    gcd_div(a, b - a);
  }
}

lemma gcd_commutative(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, b) == gcd(b, a)
{
}

lemma gcd_absorbs_multiple(a: int, b: int, k: int)
  requires a > 0 && b > 0 && k > 0
  requires b == k * a
  ensures gcd(a, b) == a
{
}

lemma gcd_same(a: int, b: int)
  requires a > 0 && b > 0
  ensures gcd(a, a) == a
  ensures gcd(a, b) == gcd(b, a)
{
}

ghost method simplify_fraction_ghost(num: int, den: int) returns (sn: int, sd: int)
  requires num > 0 && den > 0
  ensures sn > 0 && sd > 0
  ensures gcd(sn, sd) == 1
  ensures sn * den == num * sd
{
  var g := gcd(num, den);
  gcd_pos(num, den);
  gcd_div(num, den);
  assert g > 0;
  assert num % g == 0 && den % g == 0;
  sn := num / g;
  sd := den / g;
  if !(gcd(sn, sd) == 1) {
    var g2 := gcd(sn, sd);
    gcd_pos(sn, sd);
    assert g2 > 0;
    assert g * g2 > 0;
    assert num % (g * g2) == 0 && den % (g * g2) == 0;
    assert false; // Contradiction: g should be maximal divisor
  }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: string)
    requires ValidInput(a, b, c, d)
    ensures a * d == b * c ==> result == "0/1"
    ensures a * d > b * c ==> exists numerator, denominator :: 
        numerator > 0 && denominator > 0 && 
        gcd(numerator, denominator) == 1 &&
        result == intToString(numerator) + "/" + intToString(denominator) &&
        numerator * a * d == (a * d - b * c) * denominator
    ensures a * d < b * c ==> exists numerator, denominator :: 
        numerator > 0 && denominator > 0 && 
        gcd(numerator, denominator) == 1 &&
        result == intToString(numerator) + "/" + intToString(denominator) &&
        numerator * b * c == (b * c - a * d) * denominator
// </vc-spec>
// <vc-code>
{
  if a * d == b * c {
    result := "0/1";
  } else if a * d > b * c {
    var diff1 := a * d - b * c;
    var diff2 := a * d;
    assert diff1 > 0 && diff2 > 0;
    var g := gcd(diff1, diff2);
    gcd_pos(diff1, diff2);
    gcd_div(diff1, diff2);
    assert g > 0;
    assert diff1 % g == 0 && diff2 % g == 0;
    var numerator := diff1 / g;
    var denominator := diff2 / g;
    
    // Verify the postcondition relationship
    assert numerator * diff2 == (diff1) * denominator;
    assert numerator * a * d == (a * d - b * c) * denominator;
    
    result := intToString(numerator) + "/" + intToString(denominator);
  } else {
    var diff1 := b * c - a * d;
    var diff2 := b * c;
    assert diff1 > 0 && diff2 > 0;
    var g := gcd(diff1, diff2);
    gcd_pos(diff1, diff2);
    gcd_div(diff1, diff2);
    assert g > 0;
    assert diff1 % g == 0 && diff2 % g == 0;
    var numerator := diff1 / g;
    var denominator := diff2 / g;
    
    // Verify the postcondition relationship
    assert numerator * diff2 == (diff1) * denominator;
    assert numerator * b * c == (b * c - a * d) * denominator;
    
    result := intToString(numerator) + "/" + intToString(denominator);
  }
}
// </vc-code>

