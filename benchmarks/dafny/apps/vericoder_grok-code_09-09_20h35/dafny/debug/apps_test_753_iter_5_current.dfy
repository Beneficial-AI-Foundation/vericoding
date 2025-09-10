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
  requires a >= 0 && b >= 0
  requires a != 0 || b != 0
  decreases max(a, b)
{
  if b == 0 then a else gcd(b, a % b)
}

function max(a: int, b: int): int
  requires a >= 0 && b >= 0
{
  if a > b then a else b
}

lemma gcdDivides(a: int, b: int, g: int)
  requires a >= 0 && b >= 0 && (a != 0 || b != 0) && g == gcd(a, b)
  ensures g > 0 ==> (a % g == 0 && b % g == 0)
{
  if g > 0 {
    if b == 0 {
      assert a % a == 0;
      assert a % g == 0;
    } else {
      gcdDivides(b, a % b, g);
      assert b % g == 0 && (a % b) % g == 0;
      calc {
        a % g == (b * (a / b) + (a % b)) % g == 0;
      }
    }
  }
}

function intToString(i: int): string
  decreases if i >= 0 then i + 1 else -i + 1
{
  if i < 0 then
    "-" + natToString(-i, "")
  else
    natToString(i, "")
}

function natToString(n: nat, acc: string): string
  decreases if n == 0 then |acc| else n
{
  if n == 0 then
    if acc == "" then "0" else acc
  else
    natToString(n / 10, [(48 + (n % 10)) as char] + acc)
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
  var lhs := a * d;
  var rhs := b * c;
  if lhs == rhs {
    result := "0/1";
  } else if lhs > rhs {
    var num_nz := lhs - rhs;
    var den_nz := lhs;
    var g := gcd(num_nz, den_nz);
    assert g > 0;
    gcdDivides(num_nz, den_nz, g);
    assert num_nz % g == 0 && den_nz % g == 0;
    var numerator := num_nz / g;
    var denominator := den_nz / g;
    assert numerator * a * d == (a * d - b * c) * denominator;
    result := intToString(numerator) + "/" + intToString(denominator);
  } else {
    var num_nz := rhs - lhs;
    var den_nz := rhs;
    var g := gcd(num_nz, den_nz);
    assert g > 0;
    gcdDivides(num_nz, den_nz, g);
    assert num_nz % g == 0 && den_nz % g == 0;
    var numerator := num_nz / g;
    var denominator := den_nz / g;
    assert numerator * b * c == (b * c - a * d) * denominator;
    result := intToString(numerator) + "/" + intToString(denominator);
  }
}
// </vc-code>

