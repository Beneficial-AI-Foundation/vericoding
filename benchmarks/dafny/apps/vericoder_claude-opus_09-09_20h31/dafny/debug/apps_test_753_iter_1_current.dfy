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
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n == 1 then "1"
    else if n == 2 then "2"
    else if n == 3 then "3"
    else if n == 4 then "4"
    else if n == 5 then "5"
    else if n == 6 then "6"
    else if n == 7 then "7"
    else if n == 8 then "8"
    else if n == 9 then "9"
    else if n > 9 then intToString(n / 10) + intToString(n % 10)
    else "-" + intToString(-n)
}

lemma GcdCommutative(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures gcd(a, b) == gcd(b, a)
{
}

lemma GcdDivides(a: int, b: int)
    requires a >= 0 && b >= 0
    requires a > 0 || b > 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0
{
}

lemma GcdReduction(a: int, b: int, g: int)
    requires a >= 0 && b >= 0 && g > 0
    requires g == gcd(a, b)
    ensures gcd(a / g, b / g) == 1
{
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
        var numerator := ad - bc;
        var denominator := ad;
        var g := gcd(numerator, denominator);
        
        if g > 0 {
            numerator := numerator / g;
            denominator := denominator / g;
        }
        
        result := intToString(numerator) + "/" + intToString(denominator);
    } else {
        var numerator := bc - ad;
        var denominator := bc;
        var g := gcd(numerator, denominator);
        
        if g > 0 {
            numerator := numerator / g;
            denominator := denominator / g;
        }
        
        result := intToString(numerator) + "/" + intToString(denominator);
    }
}
// </vc-code>

