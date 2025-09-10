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
  ensures (a == 0 && b == 0) ==> gcd(a, b) == 0
  ensures (a == 0 && b != 0) ==> gcd(a, b) == b
  ensures (a != 0 && b == 0) ==> gcd(a, b) == a
  ensures (a > 0 && b > 0) ==> gcd(a, b) > 0
  ensures (a > 0 && b > 0) ==> (a % gcd(a, b) == 0 && b % gcd(a, b) == 0)
  ensures (a > 0 && b > 0) ==> forall k: int :: (k > 0 && a % k == 0 && b % k == 0) ==> k <= gcd(a, b)
{
  if a == 0 then b
  else if b == 0 then a
  else if a == b then a
  else if a > b then gcd(a - b, b)
  else gcd(a, b - a)
}

function intToString(n: int): string
  requires n >= 0
  ensures n == 0 ==> intToString(n) == "0"
  ensures n > 0 ==> intToString(n) != "0"
{
  if n == 0 then "0"
  else 
    var s := "";
    var temp_n := n;
    while temp_n > 0
      invariant temp_n >= 0
      invariant temp_n <= n
      invariant forall digit_char :: digit_char in s.Chars ==> digit_char >= '0' && digit_char <= '9'
      invariant (temp_n == 0 && s != "") || (temp_n > 0 && s == "") || (temp_n > 0 && s != "")
      invariant n >= temp_n
      invariant s == "" || n == (temp_n * (10 as int) power s.Length) + ParseInt(s)
    {
      s := (temp_n % 10).ToString() + s;
      temp_n := temp_n / 10;
    }
    s
}

function ParseInt(s: string): int
  requires forall k :: 0 <= k < s.Length ==> '0' <= s[k] <= '9'
{
  if s == "" then 0
  else (s[0] as int - '0' as int) * (10 as int) power (s.Length - 1) + ParseInt(s[1..])
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
    } else if ad > bc {
        var num_val := ad - bc;
        var den_val := ad;
        var common_divisor := gcd(num_val, den_val);
        var numerator := num_val / common_divisor;
        var denominator := den_val / common_divisor;
        result := intToString(numerator) + "/" + intToString(denominator);
        assert denominator > 0;
        assert numerator > 0;
        assert gcd(numerator, denominator) == 1;
        assert numerator * ad == (ad - bc) * denominator;
    } else { // ad < bc
        var num_val := bc - ad;
        var den_val := bc;
        var common_divisor := gcd(num_val, den_val);
        var numerator := num_val / common_divisor;
        var denominator := den_val / common_divisor;
        result := intToString(numerator) + "/" + intToString(denominator);
        assert denominator > 0;
        assert numerator > 0;
        assert gcd(numerator, denominator) == 1;
        assert numerator * bc == (bc - ad) * denominator;
    }
}
// </vc-code>

