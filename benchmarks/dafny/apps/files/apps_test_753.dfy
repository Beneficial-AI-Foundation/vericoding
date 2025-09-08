Given a monitor with aspect ratio a:b and a movie with aspect ratio c:d,
fit the movie on screen while preserving its aspect ratio and maximizing area.
Calculate the ratio of empty screen area to total screen area as an irreducible fraction.

predicate ValidInput(a: int, b: int, c: int, d: int) {
    a > 0 && b > 0 && c > 0 && d > 0
}

predicate IsValidFractionString(s: string, num: int, den: int) {
    num >= 0 && den > 0 && 
    gcd(num, den) == 1 &&
    s == intToString(num) + "/" + intToString(den)
}

function gcd(a: int, b: int): int
    requires a >= 0 && b >= 0
    requires a > 0 || b > 0
    ensures gcd(a, b) > 0
    ensures gcd(a, b) <= a || a == 0
    ensures gcd(a, b) <= b || b == 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else if a >= b then gcd(a - b, b)
    else gcd(a, b - a)
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n, "")
    else intToStringHelper(n, "")
}

function intToStringHelper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else intToStringHelper(n / 10, [('0' as int + n % 10) as char] + acc)
}

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
{
    if a * d == b * c {
        result := "0/1";
    } else if a * d > b * c {
        // Screen is wider relative to height than movie
        var numerator := a * d - b * c;
        var denominator := a * d;
        assert numerator > 0;
        assert denominator > 0;
        var g := gcd(numerator, denominator);
        assert g > 0;
        numerator := numerator / g;
        denominator := denominator / g;
        assert numerator > 0;
        assert denominator > 0;
        assert gcd(numerator, denominator) == 1;
        assert numerator * a * d == (a * d - b * c) * denominator;
        var tmpCall1 := intToString(numerator);
        var tmpCall2 := intToString(denominator);
        result := tmpCall1 + "/" + tmpCall2;
    } else {
        // Screen is taller relative to width than movie
        var numerator := b * c - a * d;
        var denominator := b * c;
        assert numerator > 0;
        assert denominator > 0;
        var g := gcd(numerator, denominator);
        assert g > 0;
        numerator := numerator / g;
        denominator := denominator / g;
        assert numerator > 0;
        assert denominator > 0;
        assert gcd(numerator, denominator) == 1;
        assert numerator * b * c == (b * c - a * d) * denominator;
        var tmpCall3 := intToString(numerator);
        var tmpCall4 := intToString(denominator);
        result := tmpCall3 + "/" + tmpCall4;
    }
}
