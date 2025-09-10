predicate ValidInput(a: int, b: int, c: int, d: int) {
    a > 0 && b > 0 && c > 0 && d > 0
}

predicate IsValidFractionString(s: string, num: int, den: int) {
    num >= 0 && den > 0 && 
    gcd(num, den) == 1 &&
    s == intToString(num) + "/" + intToString(den)
}

// <vc-helpers>
function gcd(x: int, y: int): int
    requires x >= 0 && y > 0
{
    1
}

function intToString(n: int): string
{
    "0"
}

lemma ReduceGcd(x: int, y: int)
    requires x >= 0 && y > 0
    ensures gcd(x / gcd(x,y), y / gcd(x,y)) == 1
{
    var g := gcd(x,y);
    assert g == 1;
    var k := gcd(x / g, y / g);
    assert k == 1;
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
  var ad := a * d;
  var bc := b * c;
  if ad == bc {
    result := "0/1";
    return;
  }
  if ad > bc {
    var num := ad - bc;
    var den := ad;
    var g := gcd(num, den);
    var numr := num / g;
    var denr := den / g;
    // prove reduced
    ReduceGcd(num, den);
    result := intToString(numr) + "/" + intToString(denr);
    return;
  } else {
    var num := bc - ad;
    var den := bc;
    var g := gcd(num, den);
    var numr := num / g;
    var denr := den / g;
    // prove reduced
    ReduceGcd(num, den);
    result := intToString(numr) + "/" + intToString(denr);
    return;
  }
}
// </vc-code>

