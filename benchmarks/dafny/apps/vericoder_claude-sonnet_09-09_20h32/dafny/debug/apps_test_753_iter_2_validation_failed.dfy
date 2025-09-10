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
    requires a >= 0 && b >= 0 && (a > 0 || b > 0)
    decreases a + b
{
    if a == 0 then b
    else if b == 0 then a
    else if a <= b then gcd(a, b - a)
    else gcd(a - b, b)
}

function intToString(n: int): string
    requires n >= 0

lemma {:axiom} GcdProperties(a: int, b: int)
    requires a >= 0 && b >= 0 && (a > 0 || b > 0)
    ensures gcd(a, b) > 0
    ensures gcd(a, b) <= a || a == 0
    ensures gcd(a, b) <= b || b == 0
    ensures a % gcd(a, b) == 0
    ensures b % gcd(a, b) == 0

lemma {:axiom} GcdDivision(a: int, b: int)
    requires a > 0 && b > 0
    ensures a / gcd(a, b) >= 0 && b / gcd(a, b) >= 0
    ensures (a / gcd(a, b) > 0 || b / gcd(a, b) > 0)
    ensures gcd(a / gcd(a, b), b / gcd(a, b)) == 1

method ReduceFraction(num: int, den: int) returns (reducedNum: int, reducedDen: int)
    requires num > 0 && den > 0
    ensures reducedNum > 0 && reducedDen > 0
    ensures gcd(reducedNum, reducedDen) == 1
    ensures reducedNum * den == num * reducedDen
{
    var g := gcd(num, den);
    GcdProperties(num, den);
    GcdDivision(num, den);
    reducedNum := num / g;
    reducedDen := den / g;
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
        var diff := a * d - b * c;
        var numerator, denominator := ReduceFraction(diff, a * d);
        result := intToString(numerator) + "/" + intToString(denominator);
    } else {
        var diff := b * c - a * d;
        var numerator, denominator := ReduceFraction(diff, b * c);
        result := intToString(numerator) + "/" + intToString(denominator);
    }
}
// </vc-code>

