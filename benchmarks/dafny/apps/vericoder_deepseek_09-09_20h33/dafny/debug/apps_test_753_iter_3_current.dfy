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
  decreases a + b
{
  if a == b then
    a
  else if a > b then
    gcd(a - b, b)
  else
    gcd(a, b - a)
}

function intToString(n: int): string

lemma gcd_lemma(a: int, b: int, c: int)
  requires a > 0 && b > 0 && c > 0
  ensures gcd(a * c, b * c) == c * gcd(a, b)
  decreases a + b + c
{
  if a == b {
  } else if a > b {
    gcd_lemma(a - b, b, c);
  } else {
    gcd_lemma(a, b - a, c);
  }
}

lemma simplify_fraction(num: int, den: int) returns (sn: int, sd: int)
  requires num > 0 && den > 0
  ensures sn > 0 && sd > 0
  ensures gcd(sn, sd) == 1
  ensures sn * den == num * sd
  decreases num + den
{
  var g := gcd(num, den);
  sn := num / g;
  sd := den / g;
}

lemma abs_lemma(x: int, y: int)
  ensures x - y > 0 || y - x > 0 || x == y
{
}

ghost method simplify_fraction_ghost(num: int, den: int) returns (sn: int, sd: int)
  requires num > 0 && den > 0
  ensures sn > 0 && sd > 0
  ensures gcd(sn, sd) == 1
  ensures sn * den == num * sd
{
  var g := gcd(num, den);
  sn := num / g;
  sd := den / g;
}
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
    ghost var sn, sd := simplify_fraction_ghost(diff1, diff2);
    result := intToString(diff1 / gcd(diff1, diff2)) + "/" + intToString(diff2 / gcd(diff1, diff2));
  } else {
    var diff1 := b * c - a * d;
    var diff2 := b * c;
    ghost var sn, sd := simplify_fraction_ghost(diff1, diff2);
    result := intToString(diff1 / gcd(diff1, diff2)) + "/" + intToString(diff2 / gcd(diff1, diff2));
  }
}
// </vc-code>

